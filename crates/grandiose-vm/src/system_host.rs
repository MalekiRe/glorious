use std::{
    ffi::{OsStr, OsString},
    fmt,
    fs::File,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    sync::{
        Mutex,
        atomic::{AtomicU64, Ordering},
    },
};

use rustix::fs::{Mode, OFlags, openat, renameat, unlinkat};

use crate::{Host, HostFault};

/// Conservative allocation and output bounds applied independently to each host call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HostLimits {
    pub max_argument_count: usize,
    pub max_argument_bytes: usize,
    pub max_file_bytes: usize,
    pub max_diagnostic_bytes: usize,
    pub max_path_bytes: usize,
    pub max_fault_message_bytes: usize,
}

impl Default for HostLimits {
    fn default() -> Self {
        Self {
            max_argument_count: 4_096,
            max_argument_bytes: 1024 * 1024,
            max_file_bytes: 64 * 1024 * 1024,
            max_diagnostic_bytes: 1024 * 1024,
            max_path_bytes: 16 * 1024,
            max_fault_message_bytes: 16 * 1024,
        }
    }
}

/// The generation-1 command-line host.
///
/// Program arguments are retained in their native representation. Conversion to UTF-8 is
/// intentionally deferred until the program actually invokes `process.args/get`.
pub struct SystemHost {
    args: Vec<OsString>,
    limits: HostLimits,
    diagnostics: Mutex<Box<dyn Write + Send>>,
}

impl SystemHost {
    pub fn new(args: Vec<OsString>) -> Self {
        Self::with_limits(args, HostLimits::default())
    }

    pub fn with_limits(args: Vec<OsString>, limits: HostLimits) -> Self {
        Self {
            args,
            limits,
            diagnostics: Mutex::new(Box::new(io::stderr())),
        }
    }

    /// Replaces the diagnostic sink. This is primarily useful to embedders and tests.
    pub fn with_diagnostic_writer(mut self, writer: impl Write + Send + 'static) -> Self {
        self.diagnostics = Mutex::new(Box::new(writer));
        self
    }

    fn fault(&self, arguments: fmt::Arguments<'_>) -> HostFault {
        use fmt::Write as _;

        let mut message = BoundedMessage::new(self.limits.max_fault_message_bytes);
        let _ = message.write_fmt(arguments);
        HostFault::new(message.text)
    }

    fn file_path(&self, path: String, operation: &str) -> Result<PathBuf, HostFault> {
        if path.is_empty() {
            return Err(self.fault(format_args!("{operation}: path must not be empty")));
        }
        if path.len() > self.limits.max_path_bytes {
            return Err(self.fault(format_args!(
                "{operation}: path exceeds per-call byte limit of {}",
                self.limits.max_path_bytes
            )));
        }
        Ok(PathBuf::from(path))
    }

    fn io_fault(&self, operation: &str, path: &Path, error: io::Error) -> HostFault {
        self.fault(format_args!("{operation}: {}: {error}", path.display()))
    }

    fn file_size_fault(&self, operation: &str, path: &Path) -> HostFault {
        self.fault(format_args!(
            "{operation}: {} exceeds per-call byte limit of {}",
            path.display(),
            self.limits.max_file_bytes
        ))
    }

    fn fs_write_relative_to_parent(
        &self,
        path: &Path,
        contents: &[u8],
        after_parent_open: impl FnOnce() -> io::Result<()>,
    ) -> Result<(), HostFault> {
        let parent = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let file_name = path
            .file_name()
            .filter(|name| !name.is_empty())
            .ok_or_else(|| {
                self.fault(format_args!(
                    "fs.write: {} has no file name",
                    path.display()
                ))
            })?;
        let parent = openat(
            rustix::fs::CWD,
            parent,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::CLOEXEC | OFlags::NOFOLLOW,
            Mode::empty(),
        )
        .map_err(|error| self.io_fault("fs.write", path, io::Error::from(error)))?;
        after_parent_open().map_err(|error| self.io_fault("fs.write", path, error))?;

        let mut temporary = None;
        for _ in 0..128 {
            let nonce = WRITE_TEMP_NONCE.fetch_add(1, Ordering::Relaxed);
            let name = OsString::from(format!(".grandiose-write-{}-{nonce}", std::process::id()));
            match openat(
                &parent,
                &name,
                OFlags::WRONLY | OFlags::CREATE | OFlags::EXCL | OFlags::CLOEXEC | OFlags::NOFOLLOW,
                Mode::from_raw_mode(0o600),
            ) {
                Ok(file) => {
                    temporary = Some((name, File::from(file)));
                    break;
                }
                Err(rustix::io::Errno::EXIST) => {}
                Err(error) => {
                    return Err(self.io_fault("fs.write", path, io::Error::from(error)));
                }
            }
        }
        let (temporary_name, mut temporary_file) = temporary.ok_or_else(|| {
            self.fault(format_args!(
                "fs.write: {}: could not allocate a temporary file",
                path.display()
            ))
        })?;
        let cleanup = TemporaryCleanup {
            parent: &parent,
            name: &temporary_name,
        };

        temporary_file
            .write_all(contents)
            .and_then(|()| temporary_file.flush())
            .and_then(|()| temporary_file.sync_all())
            .map_err(|error| self.io_fault("fs.write", path, error))?;
        renameat(&parent, &temporary_name, &parent, file_name)
            .map_err(|error| self.io_fault("fs.write", path, io::Error::from(error)))?;
        cleanup.disarm();
        Ok(())
    }
}

static WRITE_TEMP_NONCE: AtomicU64 = AtomicU64::new(0);

struct TemporaryCleanup<'a, Fd: std::os::fd::AsFd> {
    parent: &'a Fd,
    name: &'a OsStr,
}

impl<Fd: std::os::fd::AsFd> TemporaryCleanup<'_, Fd> {
    fn disarm(self) {
        std::mem::forget(self);
    }
}

impl<Fd: std::os::fd::AsFd> Drop for TemporaryCleanup<'_, Fd> {
    fn drop(&mut self) {
        let _ = unlinkat(self.parent, self.name, rustix::fs::AtFlags::empty());
    }
}

impl Host for SystemHost {
    fn process_args(&self) -> Result<Vec<String>, HostFault> {
        if self.args.len() > self.limits.max_argument_count {
            return Err(self.fault(format_args!(
                "process.args: argument count exceeds per-call limit of {}",
                self.limits.max_argument_count
            )));
        }
        let mut byte_count = 0usize;
        let mut args = Vec::new();
        args.try_reserve_exact(self.args.len()).map_err(|_| {
            self.fault(format_args!(
                "process.args: could not allocate argument result"
            ))
        })?;
        for (index, arg) in self.args.iter().enumerate() {
            let arg = arg.to_str().ok_or_else(|| {
                self.fault(format_args!(
                    "process.args: argument {index} is not valid UTF-8"
                ))
            })?;
            byte_count = byte_count.checked_add(arg.len()).ok_or_else(|| {
                self.fault(format_args!("process.args: total argument size overflowed"))
            })?;
            if byte_count > self.limits.max_argument_bytes {
                return Err(self.fault(format_args!(
                    "process.args: arguments exceed per-call byte limit of {}",
                    self.limits.max_argument_bytes
                )));
            }
            args.push(arg.to_owned());
        }
        Ok(args)
    }

    fn fs_read(&self, path: String) -> Result<Vec<u8>, HostFault> {
        let path = self.file_path(path, "fs.read")?;
        let mut file = File::open(&path).map_err(|error| self.io_fault("fs.read", &path, error))?;
        if file
            .metadata()
            .map_err(|error| self.io_fault("fs.read", &path, error))?
            .len()
            > u64::try_from(self.limits.max_file_bytes).unwrap_or(u64::MAX)
        {
            return Err(self.file_size_fault("fs.read", &path));
        }
        let mut contents = Vec::new();
        let mut buffer = [0u8; 8192];
        loop {
            let remaining = self.limits.max_file_bytes - contents.len();
            let probe = buffer.len().min(remaining.saturating_add(1));
            let read = file
                .read(&mut buffer[..probe])
                .map_err(|error| self.io_fault("fs.read", &path, error))?;
            if read == 0 {
                break;
            }
            if read > remaining {
                return Err(self.file_size_fault("fs.read", &path));
            }
            contents.try_reserve_exact(read).map_err(|_| {
                self.fault(format_args!("fs.read: could not allocate file contents"))
            })?;
            contents.extend_from_slice(&buffer[..read]);
        }
        Ok(contents)
    }

    fn fs_write(&self, path: String, contents: Vec<u8>) -> Result<(), HostFault> {
        let path = self.file_path(path, "fs.write")?;
        if contents.len() > self.limits.max_file_bytes {
            return Err(self.fault(format_args!(
                "fs.write: contents exceed per-call byte limit of {}",
                self.limits.max_file_bytes
            )));
        }
        self.fs_write_relative_to_parent(&path, &contents, || Ok(()))
    }

    fn diagnostic_write(&self, message: String) -> Result<(), HostFault> {
        if message.len() > self.limits.max_diagnostic_bytes {
            return Err(self.fault(format_args!(
                "diagnostic.write: message exceeds per-call byte limit of {}",
                self.limits.max_diagnostic_bytes
            )));
        }
        let mut diagnostics = self.diagnostics.lock().map_err(|_| {
            self.fault(format_args!(
                "diagnostic.write: diagnostic sink is unavailable"
            ))
        })?;
        diagnostics
            .write_all(message.as_bytes())
            .and_then(|()| diagnostics.flush())
            .map_err(|error| self.fault(format_args!("diagnostic.write: {error}")))
    }
}

struct BoundedMessage {
    text: String,
    limit: usize,
}

impl BoundedMessage {
    fn new(limit: usize) -> Self {
        Self {
            text: String::new(),
            limit,
        }
    }
}

impl fmt::Write for BoundedMessage {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        let remaining = self.limit.saturating_sub(self.text.len());
        let mut end = remaining.min(value.len());
        while !value.is_char_boundary(end) {
            end -= 1;
        }
        self.text.push_str(&value[..end]);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Mutex};

    use tempfile::tempdir;

    use super::*;

    #[derive(Clone, Default)]
    struct SharedWriter(Arc<Mutex<Vec<u8>>>);

    impl Write for SharedWriter {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.0.lock().unwrap().extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    fn limits(max_file_bytes: usize) -> HostLimits {
        HostLimits {
            max_file_bytes,
            ..HostLimits::default()
        }
    }

    #[test]
    fn reads_up_to_but_not_beyond_the_per_call_limit() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("input");
        std::fs::write(&path, b"four").unwrap();
        let host = SystemHost::with_limits(vec![], limits(4));
        assert_eq!(
            host.fs_read(path.to_string_lossy().into()).unwrap(),
            b"four"
        );

        std::fs::write(&path, b"five!").unwrap();
        let fault = host.fs_read(path.to_string_lossy().into()).unwrap_err();
        assert!(fault.message.starts_with("fs.read:"));
        assert!(fault.message.contains("limit of 4"));
    }

    #[test]
    fn atomically_replaces_a_file_and_preserves_it_on_precommit_failure() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("output");
        std::fs::write(&path, b"old").unwrap();
        let host = SystemHost::with_limits(vec![], limits(3));

        host.fs_write(path.to_string_lossy().into(), b"new".to_vec())
            .unwrap();
        assert_eq!(std::fs::read(&path).unwrap(), b"new");

        let fault = host
            .fs_write(path.to_string_lossy().into(), b"large".to_vec())
            .unwrap_err();
        assert!(fault.message.starts_with("fs.write:"));
        assert_eq!(std::fs::read(&path).unwrap(), b"new");
        assert_eq!(std::fs::read_dir(directory.path()).unwrap().count(), 1);
    }

    #[test]
    fn failed_commit_cleans_up_the_same_directory_temporary_file() {
        let directory = tempdir().unwrap();
        let target = directory.path().join("existing-directory");
        std::fs::create_dir(&target).unwrap();
        let host = SystemHost::new(vec![]);

        let fault = host
            .fs_write(target.to_string_lossy().into(), b"data".to_vec())
            .unwrap_err();
        assert!(fault.message.starts_with("fs.write:"));
        assert!(target.is_dir());
        assert_eq!(std::fs::read_dir(directory.path()).unwrap().count(), 1);
    }

    #[cfg(unix)]
    #[test]
    fn write_stays_with_the_open_parent_when_its_path_is_replaced_by_a_symlink() {
        use std::os::unix::fs::symlink;

        let directory = tempdir().unwrap();
        let victim = directory.path().join("victim");
        let moved_victim = directory.path().join("moved-victim");
        let attacker = directory.path().join("attacker");
        std::fs::create_dir(&victim).unwrap();
        std::fs::create_dir(&attacker).unwrap();
        std::fs::write(victim.join("output"), b"victim-old").unwrap();
        std::fs::write(attacker.join("output"), b"attacker-old").unwrap();
        let target = victim.join("output");
        let host = SystemHost::new(vec![]);

        host.fs_write_relative_to_parent(&target, b"victim-new", || {
            std::fs::rename(&victim, &moved_victim)?;
            symlink(&attacker, &victim)
        })
        .unwrap();

        assert_eq!(
            std::fs::read(moved_victim.join("output")).unwrap(),
            b"victim-new"
        );
        assert_eq!(
            std::fs::read(attacker.join("output")).unwrap(),
            b"attacker-old"
        );
        assert_eq!(std::fs::read_dir(&moved_victim).unwrap().count(), 1);
    }

    #[cfg(unix)]
    #[test]
    fn write_rejects_a_symlink_as_the_immediate_parent() {
        use std::os::unix::fs::symlink;

        let directory = tempdir().unwrap();
        let attacker = directory.path().join("attacker");
        let alias = directory.path().join("alias");
        std::fs::create_dir(&attacker).unwrap();
        std::fs::write(attacker.join("output"), b"old").unwrap();
        symlink(&attacker, &alias).unwrap();
        let host = SystemHost::new(vec![]);

        let fault = host
            .fs_write(
                alias.join("output").to_string_lossy().into(),
                b"new".to_vec(),
            )
            .unwrap_err();

        assert!(fault.message.starts_with("fs.write:"));
        assert_eq!(std::fs::read(attacker.join("output")).unwrap(), b"old");
        assert_eq!(std::fs::read_dir(&attacker).unwrap().count(), 1);
    }

    #[test]
    fn diagnostics_are_exact_and_bounded() {
        let writer = SharedWriter::default();
        let captured = writer.0.clone();
        let host = SystemHost::with_limits(
            vec![],
            HostLimits {
                max_diagnostic_bytes: 4,
                ..HostLimits::default()
            },
        )
        .with_diagnostic_writer(writer);

        host.diagnostic_write("text".into()).unwrap();
        assert_eq!(&*captured.lock().unwrap(), b"text");
        assert!(host.diagnostic_write("large".into()).is_err());
        assert_eq!(&*captured.lock().unwrap(), b"text");
    }

    #[test]
    fn paths_and_fault_messages_are_bounded_before_io() {
        let host = SystemHost::with_limits(
            vec![],
            HostLimits {
                max_path_bytes: 3,
                max_fault_message_bytes: 19,
                ..HostLimits::default()
            },
        );

        let fault = host.fs_read("four".into()).unwrap_err();
        assert!(fault.message.len() <= 19);
        assert!(fault.message.is_char_boundary(fault.message.len()));
        assert!(fault.message.starts_with("fs.read: path"));
    }

    #[test]
    fn bounded_faults_do_not_split_utf8() {
        let host = SystemHost::with_limits(
            vec![],
            HostLimits {
                max_fault_message_bytes: 2,
                ..HostLimits::default()
            },
        );
        let fault = host.fault(format_args!("éé"));
        assert_eq!(fault.message, "é");
    }

    #[cfg(unix)]
    #[test]
    fn native_arguments_are_decoded_only_when_requested() {
        use std::os::unix::ffi::OsStringExt;

        let host = SystemHost::new(vec![OsString::from_vec(vec![0xff])]);
        let fault = host.process_args().unwrap_err();
        assert_eq!(fault.message, "process.args: argument 0 is not valid UTF-8");
    }
}
