//! Content-Length framed JSON-RPC over arbitrary streams (LSP base protocol).

use std::io::{BufRead, Write};

use anyhow::{bail, Context, Result};
use serde_json::Value;

/// Read one message; `None` on clean EOF.
pub fn read_message(input: &mut impl BufRead) -> Result<Option<Value>> {
    let mut content_length: Option<usize> = None;
    loop {
        let mut line = String::new();
        if input.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some(value) = line.strip_prefix("Content-Length:") {
            content_length = Some(value.trim().parse().context("bad Content-Length")?);
        }
    }
    let length = content_length.context("missing Content-Length header")?;
    let mut body = vec![0u8; length];
    input.read_exact(&mut body)?;
    let value = serde_json::from_slice(&body).context("malformed JSON-RPC body")?;
    Ok(Some(value))
}

pub fn write_message(output: &mut impl Write, message: &Value) -> Result<()> {
    let body = serde_json::to_vec(message)?;
    write!(output, "Content-Length: {}\r\n\r\n", body.len())?;
    output.write_all(&body)?;
    output.flush()?;
    Ok(())
}

/// `file://` URI to filesystem path (percent-decoded).
pub fn uri_to_path(uri: &str) -> Result<std::path::PathBuf> {
    let Some(rest) = uri.strip_prefix("file://") else {
        bail!("unsupported URI scheme: {uri}");
    };
    let mut bytes = Vec::new();
    let mut chars = rest.bytes();
    while let Some(byte) = chars.next() {
        if byte == b'%' {
            let high = chars.next().context("truncated percent-escape")?;
            let low = chars.next().context("truncated percent-escape")?;
            let hex = [high, low];
            let hex = std::str::from_utf8(&hex)?;
            bytes.push(u8::from_str_radix(hex, 16)?);
        } else {
            bytes.push(byte);
        }
    }
    Ok(std::path::PathBuf::from(String::from_utf8(bytes)?))
}

pub fn path_to_uri(path: &std::path::Path) -> String {
    let mut out = String::from("file://");
    for byte in path.to_string_lossy().bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'/' | b'.' | b'-' | b'_' | b'~' => {
                out.push(byte as char)
            }
            other => out.push_str(&format!("%{other:02X}")),
        }
    }
    out
}
