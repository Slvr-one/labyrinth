//! Process execution, temporary directories and directory copying.

use std::ffi::OsStr;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{fs, io};

pub type Env = Vec<(String, String)>;

pub struct Output {
    pub code: i32,
    pub text: String,
}

/// Run `program` with a fixed argv, echo `+ command`, stream the merged stdout/stderr, capture it.
/// A non-zero exit is an error unless `allow_failure`.
pub fn run(
    program: &str,
    args: &[&str],
    cwd: &Path,
    env: &Env,
    allow_failure: bool,
) -> Result<Output, String> {
    println!("+ {program} {}", args.join(" "));
    let (reader, writer) = io::pipe().map_err(|e| format!("pipe: {e}"))?;
    let mut command = Command::new(program);
    command
        .args(args)
        .current_dir(cwd)
        .envs(env.iter().map(|(k, v)| (k, v)))
        .stdin(Stdio::null())
        .stdout(writer.try_clone().map_err(|e| format!("pipe: {e}"))?)
        .stderr(writer);
    let mut child = command
        .spawn()
        .map_err(|e| format!("cannot start {program}: {e}"))?;
    drop(command);
    let mut text = String::new();
    for line in BufReader::new(reader).split(b'\n') {
        let line = line.map_err(|e| format!("reading {program} output: {e}"))?;
        let line = String::from_utf8_lossy(&line);
        println!("{line}");
        text.push_str(&line);
        text.push('\n');
    }
    let status = child
        .wait()
        .map_err(|e| format!("waiting for {program}: {e}"))?;
    let code = status.code().unwrap_or(-1);
    if code != 0 && !allow_failure {
        return Err(format!(
            "`{program} {}` exited with status {code}",
            args.join(" ")
        ));
    }
    Ok(Output { code, text })
}

pub struct TempDir(PathBuf);

impl TempDir {
    pub fn new(prefix: &str) -> Result<Self, String> {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.subsec_nanos());
        let path = std::env::temp_dir().join(format!("{prefix}{}-{nanos}", std::process::id()));
        fs::create_dir(&path).map_err(|e| format!("cannot create {}: {e}", path.display()))?;
        Ok(Self(path))
    }

    pub fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Recursively copy `from` into `to`, skipping `target` directories and `*.llbc` files.
pub fn copy_rust_tree(from: &Path, to: &Path) -> io::Result<()> {
    fs::create_dir_all(to)?;
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let name = entry.file_name();
        let skip = name == OsStr::new("target")
            || Path::new(&name).extension() == Some(OsStr::new("llbc"));
        if skip {
            continue;
        }
        let destination = to.join(&name);
        if entry.metadata()?.is_dir() {
            copy_rust_tree(&entry.path(), &destination)?;
        } else {
            fs::copy(entry.path(), destination)?;
        }
    }
    Ok(())
}
