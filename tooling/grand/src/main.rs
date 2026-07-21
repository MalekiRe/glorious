use anyhow::Result;
use clap::{Args, Parser, Subcommand};
use grand::ops::{self, LintLevel};
use grand::target::Target;

/// Diagnostic level overrides, applied over the manifest's `[lints]` table.
/// Precedence within the CLI: --allow, then --warn, then --deny.
#[derive(Args, Default)]
struct LintArgs {
    /// Silence a diagnostic code, or `warnings` for all warnings
    #[arg(short = 'A', long = "allow")]
    allow: Vec<String>,
    /// Reset a diagnostic code to warning level
    #[arg(short = 'W', long = "warn")]
    warn: Vec<String>,
    /// Escalate a diagnostic code (or `warnings`) to an error
    #[arg(short = 'D', long = "deny")]
    deny: Vec<String>,
}

impl LintArgs {
    fn levels(&self) -> Vec<(String, LintLevel)> {
        let tag = |codes: &[String], level| {
            codes
                .iter()
                .map(move |c| (c.clone(), level))
                .collect::<Vec<_>>()
        };
        [
            tag(&self.allow, LintLevel::Allow),
            tag(&self.warn, LintLevel::Warn),
            tag(&self.deny, LintLevel::Deny),
        ]
        .concat()
    }
}

/// Build tool for the Grandiose language.
#[derive(Parser)]
#[command(name = "grand", version, about)]
struct Cli {
    /// Workspace member to operate on (name or directory)
    #[arg(short = 'p', long = "package", global = true)]
    package: Option<String>,
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Create a new package in a new directory
    New { name: String },
    /// Create a package in the current directory
    Init,
    /// Compile the current package and its dependencies
    Build {
        /// auto (G1 VM when available), vm, interp (legacy LLVM), or native
        #[arg(long, default_value = "auto")]
        target: String,
        /// Optimization level (forwarded as -O<n> once the compiler supports it)
        #[arg(short = 'O', long = "opt")]
        opt: Option<u8>,
        #[command(flatten)]
        lints: LintArgs,
    },
    /// Build and execute the current package
    Run {
        #[arg(long, default_value = "auto")]
        target: String,
        #[arg(short = 'O', long = "opt")]
        opt: Option<u8>,
        #[command(flatten)]
        lints: LintArgs,
        /// Arguments passed to the program after `--`
        #[arg(last = true)]
        arguments: Vec<String>,
    },
    /// Compile without materializing an artifact
    Check {
        #[command(flatten)]
        lints: LintArgs,
    },
    /// Run tests: tests/*.glorious as executables (exit 0 = pass), in parallel,
    /// and tests/compile-fail/*.glorious against golden .stderr files
    Test {
        /// Only run tests whose name contains this substring
        filter: Option<String>,
        #[arg(long, default_value = "auto")]
        target: String,
        /// Rewrite compile-fail golden .stderr files with current output
        #[arg(long)]
        bless: bool,
        #[command(flatten)]
        lints: LintArgs,
    },
    /// Apply machine-applicable fixes suggested by diagnostics
    Fix {
        #[command(flatten)]
        lints: LintArgs,
    },
    /// Generate API documentation into target/grand/doc
    Doc {
        /// Open the generated docs in a browser
        #[arg(long)]
        open: bool,
    },
    /// Start the language server (delegates to the grand-lsp binary)
    Lsp,
    /// Format the package's sources in place
    Fmt {
        /// Report files that need formatting without rewriting (CI mode)
        #[arg(long)]
        check: bool,
        /// Format stdin to stdout instead of files
        #[arg(long)]
        stdin: bool,
        /// Explicit files to format (default: package sources + tests)
        paths: Vec<std::path::PathBuf>,
    },
    /// Add a dependency to grandiose.toml and the lockfile
    Add {
        name: String,
        #[arg(long)]
        path: Option<String>,
        #[arg(long)]
        git: Option<String>,
        /// Shorthand for git = https://github.com/<user/repo>
        #[arg(long)]
        github: Option<String>,
        #[arg(long)]
        tag: Option<String>,
        #[arg(long)]
        rev: Option<String>,
        #[arg(long)]
        branch: Option<String>,
    },
    /// Re-resolve branch/tag dependencies and rewrite the lockfile
    Update { packages: Vec<String> },
    /// Verify or (re)generate the lockfile without building
    Lock,
    /// Copy git dependencies into ./vendor for offline builds
    Vendor,
    /// Remove build outputs (--cache also clears the shared download cache)
    Clean {
        #[arg(long)]
        cache: bool,
    },
}

fn main() {
    let cli = Cli::parse();
    match dispatch(cli) {
        Ok(code) => std::process::exit(code),
        Err(error) => {
            eprintln!("error: {error:#}");
            std::process::exit(1);
        }
    }
}

fn dispatch(cli: Cli) -> Result<i32> {
    ops::select_package(cli.package.clone());
    match cli.command {
        Command::New { name } => ops::new(&name).map(|()| 0),
        Command::Init => ops::init().map(|()| 0),
        Command::Build { target, opt, lints } => {
            ops::build(Target::parse(&target)?, opt, &lints.levels()).map(|()| 0)
        }
        Command::Run {
            target,
            opt,
            lints,
            arguments,
        } => ops::run(Target::parse(&target)?, arguments, opt, &lints.levels()),
        Command::Check { lints } => ops::check(&lints.levels()).map(|()| 0),
        Command::Test {
            filter,
            target,
            bless,
            lints,
        } => ops::test(
            Target::parse(&target)?,
            filter.as_deref(),
            bless,
            &lints.levels(),
        ),
        Command::Fix { lints } => ops::fix(&lints.levels()).map(|()| 0),
        Command::Doc { open } => ops::doc(open).map(|()| 0),
        Command::Fmt {
            check,
            stdin,
            paths,
        } => if stdin {
            ops::fmt_stdin()
        } else {
            ops::fmt(check, paths)
        }
        .map(|()| 0),
        Command::Lsp => {
            // Prefer a grand-lsp sitting next to this binary, then PATH.
            let sibling = std::env::current_exe()
                .ok()
                .and_then(|exe| Some(exe.parent()?.join("grand-lsp")))
                .filter(|p| p.is_file());
            let program = sibling.unwrap_or_else(|| "grand-lsp".into());
            let status = std::process::Command::new(program).status()?;
            Ok(status.code().unwrap_or(1))
        }
        Command::Add {
            name,
            path,
            git,
            github,
            tag,
            rev,
            branch,
        } => ops::add(ops::AddSpec {
            name,
            path,
            git,
            github,
            tag,
            rev,
            branch,
        })
        .map(|()| 0),
        Command::Update { packages } => ops::update(packages).map(|()| 0),
        Command::Lock => ops::lock().map(|()| 0),
        Command::Vendor => ops::vendor().map(|()| 0),
        Command::Clean { cache } => ops::clean(cache).map(|()| 0),
    }
}
