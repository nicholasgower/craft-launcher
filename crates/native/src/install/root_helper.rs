//! One password prompt for a run of system installs.
//!
//! `pkexec` authenticates every call on its own, so updating several apps at once asks for the
//! password once per app. The first call instead starts this program again as root, through a
//! single `pkexec`, and keeps it running as a helper. Later installs and removals go through
//! that helper, until it has been idle for fifteen minutes or the launcher exits. The password
//! never reaches the launcher: the desktop's polkit agent asks for it once.
//!
//! The helper runs only a fixed set of commands. Its targets are either
//! downloaded package files that belong to the user who approved the prompt, or plain package
//! names, so it cannot be asked to run an arbitrary program or to give a package manager extra
//! options.

use std::ffi::{OsStr, OsString};
use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::MetadataExt;
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, ExitCode, Stdio};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::sync::{Mutex, MutexGuard, PoisonError};
use std::time::Duration;

use artcraft_launcher_core::protocol::CANCELLED;

use super::{SYSTEM_BIN_DIRS, find_in, pkexec, process, with_absolute_program};

/// The argument that turns this program into the privileged helper.
pub const FLAG: &str = "--artcraft-root-helper";

/// How long the helper waits for another install before it exits. Every request restarts it.
const IDLE: Duration = Duration::from_secs(15 * 60);

/// How long the desktop may take to collect the password before the first call gives up.
const START_LIMIT: Duration = Duration::from_secs(5 * 60);

/// The helper's first line once it is running as root with the desktop's permission. The number
/// is the protocol version, so a launcher never talks to a helper from another build.
const READY: &str = "READY 1\n";

const MAX_TARGETS: usize = 64;
const MAX_TARGET: usize = 4096;
const MAX_PAYLOAD: usize = 1 << 20;
const MAX_MESSAGE_CHARS: usize = 1000;

// Every command the helper may run, with the fixed arguments before the targets. The
// launcher's package commands are these same constants, so the two can't drift apart.
// `DPkg::Lock::Timeout=60` makes apt wait for another package tool (a software centre,
// automatic updates) to let go of its lock instead of failing at once.
pub const APT_INSTALL: &[&str] = &["apt-get", "-o", "DPkg::Lock::Timeout=60", "install", "-y", "--allow-downgrades"];
pub const APT_REMOVE: &[&str] = &["apt-get", "-o", "DPkg::Lock::Timeout=60", "remove", "-y"];
pub const DPKG_REMOVE: &[&str] = &["dpkg", "-r"];
pub const DNF_INSTALL: &[&str] = &["dnf", "install", "-y"];
pub const DNF_REMOVE: &[&str] = &["dnf", "remove", "-y"];
pub const ZYPPER_INSTALL: &[&str] = &["zypper", "--non-interactive", "install", "--allow-unsigned-rpm"];
pub const RPM_INSTALL: &[&str] = &["rpm", "-U", "--replacepkgs"];
pub const RPM_REMOVE: &[&str] = &["rpm", "-e"];
pub const PACMAN_INSTALL: &[&str] = &["pacman", "-U", "--noconfirm"];
pub const PACMAN_REMOVE: &[&str] = &["pacman", "-R", "--noconfirm"];
pub const FLATPAK_SYSTEM_UNINSTALL: &[&str] = &["flatpak", "uninstall", "--system", "-y", "--noninteractive"];

/// A command the helper may run.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RootCommand {
    AptInstall = 0,
    AptRemove = 1,
    DpkgRemove = 2,
    DnfInstall = 3,
    DnfRemove = 4,
    ZypperInstall = 5,
    RpmInstall = 6,
    RpmRemove = 7,
    PacmanInstall = 8,
    PacmanRemove = 9,
    FlatpakSystemUninstall = 10,
}

impl RootCommand {
    const ALL: [Self; 11] = [
        Self::AptInstall,
        Self::AptRemove,
        Self::DpkgRemove,
        Self::DnfInstall,
        Self::DnfRemove,
        Self::ZypperInstall,
        Self::RpmInstall,
        Self::RpmRemove,
        Self::PacmanInstall,
        Self::PacmanRemove,
        Self::FlatpakSystemUninstall,
    ];

    fn argv(self) -> &'static [&'static str] {
        match self {
            Self::AptInstall => APT_INSTALL,
            Self::AptRemove => APT_REMOVE,
            Self::DpkgRemove => DPKG_REMOVE,
            Self::DnfInstall => DNF_INSTALL,
            Self::DnfRemove => DNF_REMOVE,
            Self::ZypperInstall => ZYPPER_INSTALL,
            Self::RpmInstall => RPM_INSTALL,
            Self::RpmRemove => RPM_REMOVE,
            Self::PacmanInstall => PACMAN_INSTALL,
            Self::PacmanRemove => PACMAN_REMOVE,
            Self::FlatpakSystemUninstall => FLATPAK_SYSTEM_UNINSTALL,
        }
    }

    fn targets(self) -> Targets {
        match self {
            Self::AptInstall | Self::DnfInstall | Self::ZypperInstall | Self::RpmInstall | Self::PacmanInstall => Targets::Files,
            Self::AptRemove | Self::DpkgRemove | Self::DnfRemove | Self::RpmRemove | Self::PacmanRemove | Self::FlatpakSystemUninstall => {
                Targets::Names
            }
        }
    }

    fn from_index(index: u8) -> Option<Self> {
        Self::ALL.get(usize::from(index)).copied()
    }

    /// The command whose fixed arguments start `args`, with the rest as its targets. The
    /// longest match wins, so no shorter command can claim a longer one's call.
    fn of<'a>(args: &'a [&'a OsStr]) -> Option<(Self, Vec<&'a OsStr>)> {
        let mut found: Option<(Self, Vec<&OsStr>)> = None;
        for command in Self::ALL {
            let argv = command.argv();
            if args.len() <= argv.len() {
                continue;
            }
            if argv.iter().zip(args).all(|(expected, actual)| actual.as_bytes() == expected.as_bytes())
                && found.as_ref().is_none_or(|(best, _)| argv.len() > best.argv().len())
            {
                found = Some((command, args[argv.len()..].to_vec()));
            }
        }
        found
    }
}

/// What a command puts after its fixed arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Targets {
    /// Downloaded package files.
    Files,
    /// Package names.
    Names,
}

/// Runs the privileged helper when this program was started as one. The launcher calls this
/// before it sets anything else up; every other start has no [`FLAG`] and returns `None`.
pub fn run_if_requested() -> Option<ExitCode> {
    let requested = std::env::args_os().skip(1).any(|arg| arg.to_str() == Some(FLAG));
    requested.then(|| ExitCode::from(serve()))
}

/// The helper: announce that root is available, then do the work asked of it until the
/// launcher goes away or nothing has been asked for a while.
fn serve() -> u8 {
    // `pkexec` sets this to the user who approved the prompt. Without it this wasn't started
    // by a permission prompt, so it is not allowed to install anything.
    let Some(uid) = std::env::var("PKEXEC_UID").ok().and_then(|uid| uid.parse::<u32>().ok()) else {
        return 1;
    };
    let (sender, receiver) = mpsc::channel();
    if std::thread::Builder::new()
        .name("root-helper-input".into())
        .spawn(move || {
            let mut input = std::io::stdin().lock();
            while let Ok(request) = read_request(&mut input) {
                if sender.send(request).is_err() {
                    break;
                }
            }
        })
        .is_err()
    {
        return 1;
    }
    if std::io::stdout().write_all(READY.as_bytes()).and_then(|()| std::io::stdout().flush()).is_err() {
        return 1;
    }
    loop {
        match receiver.recv_timeout(IDLE) {
            Ok(request) => {
                if write_response(&execute(request, uid)).is_err() {
                    return 1;
                }
            }
            Err(RecvTimeoutError::Timeout | RecvTimeoutError::Disconnected) => return 0,
        }
    }
}

struct Request {
    command: RootCommand,
    targets: Vec<OsString>,
}

fn read_request(input: &mut impl Read) -> Result<Request, ()> {
    let mut header = [0u8; 4];
    input.read_exact(&mut header).map_err(|_| ())?;
    let length = u32::from_be_bytes(header) as usize;
    if length == 0 || length > MAX_PAYLOAD {
        return Err(());
    }
    let mut payload = vec![0u8; length];
    input.read_exact(&mut payload).map_err(|_| ())?;
    decode(&payload).map_err(|_| ())
}

fn decode(payload: &[u8]) -> Result<Request, String> {
    let (&index, rest) = payload.split_first().ok_or("empty request")?;
    let command = RootCommand::from_index(index).ok_or("unknown command")?;
    let mut at = 0;
    let count = take_u32(rest, &mut at)?;
    if count == 0 || count > MAX_TARGETS as u32 {
        return Err("wrong number of targets".into());
    }
    let mut targets = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let length = take_u32(rest, &mut at)? as usize;
        if length == 0 || length > MAX_TARGET {
            return Err("invalid target".into());
        }
        let end = at.checked_add(length).ok_or("truncated request")?;
        let bytes = rest.get(at..end).ok_or("truncated request")?;
        at = end;
        targets.push(OsString::from_vec(bytes.to_vec()));
    }
    if at != rest.len() {
        return Err("trailing request data".into());
    }
    Ok(Request { command, targets })
}

fn take_u32(bytes: &[u8], at: &mut usize) -> Result<u32, String> {
    let end = at.checked_add(4).ok_or("truncated request")?;
    let part = bytes.get(*at..end).ok_or("truncated request")?;
    let value = <[u8; 4]>::try_from(part).map_err(|_| "truncated request")?;
    *at = end;
    Ok(u32::from_be_bytes(value))
}

fn execute(request: Request, uid: u32) -> Result<(), String> {
    validate(request.command, &request.targets, Some(uid))?;
    let argv = request.command.argv();
    let program = find_in(&SYSTEM_BIN_DIRS, OsStr::new(argv[0])).ok_or_else(|| format!("{} isn't installed", argv[0]))?;
    let status = process::command(program)
        .args(&argv[1..])
        .args(&request.targets)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map_err(|e| format!("couldn't start {} ({e})", argv[0]))?;
    match status.code() {
        Some(0) => Ok(()),
        Some(code) => Err(format!("the system installer stopped with error {code}")),
        None => Err("the system installer was interrupted".into()),
    }
}

fn write_response(outcome: &Result<(), String>) -> std::io::Result<()> {
    let (status, message) = match outcome {
        Ok(()) => (0u8, String::new()),
        Err(error) => (1u8, error.chars().take(MAX_MESSAGE_CHARS).collect()),
    };
    let message = message.as_bytes();
    // The helper writes it, so it fits a u32 by construction; a failure here can only mean the
    // launcher is gone, which the caller handles by exiting.
    let length = u32::try_from(message.len()).unwrap_or(u32::MAX).to_be_bytes();
    let mut stdout = std::io::stdout().lock();
    stdout.write_all(&[status])?;
    stdout.write_all(&length)?;
    stdout.write_all(message)?;
    stdout.flush()
}

/// Whether `targets` is something `command` may run, checked without root before a prompt is
/// shown. The helper repeats the check with the file owner's user id.
fn validate<T: AsRef<OsStr>>(command: RootCommand, targets: &[T], uid: Option<u32>) -> Result<(), String> {
    if targets.is_empty() || targets.len() > MAX_TARGETS {
        return Err("the install request has the wrong number of files".into());
    }
    for target in targets {
        let target = target.as_ref();
        match command.targets() {
            Targets::Files => check_file(target, uid)?,
            Targets::Names => check_name(target)?,
        }
    }
    Ok(())
}

fn check_file(target: &OsStr, uid: Option<u32>) -> Result<(), String> {
    let path = Path::new(target);
    if !path.is_absolute() {
        return Err("a package to install must be an absolute path".into());
    }
    let metadata = std::fs::symlink_metadata(path).map_err(|_| format!("{} can't be installed", path.display()))?;
    if !metadata.file_type().is_file() || uid.is_some_and(|uid| metadata.uid() != uid) {
        return Err(format!("{} isn't a downloaded package of the user who approved the prompt", path.display()));
    }
    Ok(())
}

fn check_name(target: &OsStr) -> Result<(), String> {
    let Some(name) = target.to_str() else {
        return Err("a package name must be text".into());
    };
    let allowed = |byte: u8| byte.is_ascii_alphanumeric() || matches!(byte, b'+' | b'-' | b'.' | b'_' | b'@');
    if name.is_empty() || name.len() > 200 || name.starts_with('-') || !name.bytes().all(allowed) {
        return Err(format!("{name} isn't a package name"));
    }
    Ok(())
}

/// The launcher's side of the helper.
struct RootSession {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
}

/// The helper of this launcher, when it has one.
static SESSION: Mutex<Option<RootSession>> = Mutex::new(None);

fn lock() -> MutexGuard<'static, Option<RootSession>> {
    SESSION.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Runs a command that needs root. A command the helper knows is sent to it, starting it (and
/// with it the desktop's one password prompt) if needed; anything else goes through `pkexec`
/// on its own, as before.
pub fn run(args: &[&OsStr]) -> Result<(), String> {
    let Some((command, targets)) = RootCommand::of(args) else {
        return direct(args);
    };
    validate(command, &targets, None)?;
    // An AppImage's own binary lives in a temporary mount, and inside a Flatpak sandbox root
    // means the sandbox's own root: neither is a place to keep a privileged helper. Those keep
    // the per-install prompt.
    if std::env::var_os("APPIMAGE").is_some() || process::in_sandbox() {
        return direct(args);
    }
    let mut session = lock();
    if session.as_mut().is_some_and(|session| session.finished()) {
        *session = None;
    }
    if session.is_none() {
        *session = Some(RootSession::start()?);
    }
    let exchanged = match session.as_mut() {
        Some(active) => active.exchange(command, &targets),
        None => Exchange::Broken("the elevated install session wasn't available; try again".into()),
    };
    match exchanged {
        Exchange::Installed(outcome) => outcome,
        Exchange::Broken(error) => {
            *session = None;
            Err(error)
        }
    }
}

/// What one exchange with the helper says.
enum Exchange {
    /// The helper answered: the command's own outcome. The helper is still usable.
    Installed(Result<(), String>),
    /// The helper could not be reached. It is dropped; the next call asks for permission again.
    Broken(String),
}

impl RootSession {
    /// Starts the helper through polkit. `Err("cancelled")` when the prompt was dismissed.
    fn start() -> Result<Self, String> {
        let executable = std::env::current_exe().map_err(|e| format!("couldn't find this program ({e})"))?;
        let pkexec = pkexec().ok_or_else(|| "installing system-wide needs polkit (pkexec), which isn't installed".to_string())?;
        let mut child = process::command(pkexec)
            .arg(&executable)
            .arg(FLAG)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|e| format!("couldn't ask for permission ({e})"))?;
        let Some(stdout) = child.stdout.take() else {
            return Err(start_failed(&mut child, "couldn't ask for permission (no answer)"));
        };
        let Some(input) = child.stdin.take() else {
            return Err(start_failed(&mut child, "couldn't ask for permission (no answer)"));
        };
        let (sender, receiver) = mpsc::sync_channel(1);
        let reader = match std::thread::Builder::new().name("pkexec-start".into()).spawn(move || {
            let mut output = BufReader::new(stdout);
            let mut line = String::new();
            let read = output.read_line(&mut line);
            let _ = sender.send((read, line, output));
        }) {
            Ok(reader) => reader,
            Err(_) => return Err(start_failed(&mut child, "couldn't ask for permission (no answer)")),
        };
        match receiver.recv_timeout(START_LIMIT) {
            Ok((Ok(count), line, output)) if count > 0 && line == READY => {
                let _ = reader.join();
                Ok(Self { child, input, output })
            }
            // The pipe closed: `pkexec` has finished, so its exit code says why (126 and 127
            // mean the prompt was dismissed or refused).
            Ok((Ok(0), _, output)) => {
                let _ = reader.join();
                drop(output);
                let status = child.wait().map_err(|e| format!("couldn't ask for permission ({e})"))?;
                Err(start_failed_code(status.code()))
            }
            // Anything else means the helper didn't start as expected; stop it before waiting.
            Ok(_) | Err(RecvTimeoutError::Disconnected) => Err(start_failed(&mut child, "the permission prompt closed")),
            Err(RecvTimeoutError::Timeout) => Err(start_failed(&mut child, "the permission prompt wasn't answered")),
        }
    }

    fn finished(&mut self) -> bool {
        !matches!(self.child.try_wait(), Ok(None))
    }

    fn exchange(&mut self, command: RootCommand, targets: &[&OsStr]) -> Exchange {
        let payload = match encode(command, targets) {
            Ok(payload) => payload,
            Err(()) => return Exchange::Broken("the install request is too large".into()),
        };
        let length = u32::try_from(payload.len()).unwrap_or(u32::MAX).to_be_bytes();
        let written = self.input.write_all(&length).and_then(|()| self.input.write_all(&payload)).and_then(|()| self.input.flush());
        if let Err(e) = written {
            return Exchange::Broken(gone(e));
        }
        let mut status = [0u8; 1];
        if let Err(e) = self.output.read_exact(&mut status) {
            return Exchange::Broken(gone(e));
        }
        let mut length = [0u8; 4];
        if let Err(e) = self.output.read_exact(&mut length) {
            return Exchange::Broken(gone(e));
        }
        let size = u32::from_be_bytes(length) as usize;
        if size > MAX_PAYLOAD {
            return Exchange::Broken("the elevated install session sent an invalid answer; try again".into());
        }
        let mut message = vec![0u8; size];
        if let Err(e) = self.output.read_exact(&mut message) {
            return Exchange::Broken(gone(e));
        }
        match status[0] {
            0 => Exchange::Installed(Ok(())),
            1 => Exchange::Installed(Err(String::from_utf8_lossy(&message).into_owned())),
            _ => Exchange::Broken("the elevated install session sent an invalid answer; try again".into()),
        }
    }
}

/// A session that stopped answering has no useful answers left; end it. A healthy helper is
/// never dropped: it sees each command through and exits once its pipe closes or it is idle.
impl Drop for RootSession {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn gone(error: std::io::Error) -> String {
    format!("the elevated install session ended ({error}); try again")
}

fn start_failed(child: &mut Child, reason: &str) -> String {
    let _ = child.kill();
    let _ = child.wait();
    reason.to_string()
}

fn start_failed_code(code: Option<i32>) -> String {
    match code {
        Some(126 | 127) => CANCELLED.to_string(),
        Some(code) => format!("couldn't ask for permission (exit {code})"),
        None => "couldn't ask for permission (interrupted)".into(),
    }
}

/// The helper's request: the command number, then every target length-prefixed.
fn encode(command: RootCommand, targets: &[&OsStr]) -> Result<Vec<u8>, ()> {
    if targets.is_empty() || targets.len() > MAX_TARGETS {
        return Err(());
    }
    let count = u32::try_from(targets.len()).map_err(|_| ())?;
    let mut payload = Vec::new();
    payload.push(command as u8);
    payload.extend_from_slice(&count.to_be_bytes());
    for target in targets {
        let bytes = target.as_bytes();
        if bytes.is_empty() || bytes.len() > MAX_TARGET {
            return Err(());
        }
        let length = u32::try_from(bytes.len()).map_err(|_| ())?;
        payload.extend_from_slice(&length.to_be_bytes());
        payload.extend_from_slice(bytes);
    }
    if payload.len() > MAX_PAYLOAD { Err(()) } else { Ok(payload) }
}

/// A command that needs root, run on its own through `pkexec` (used where the helper can't).
fn direct(args: &[&OsStr]) -> Result<(), String> {
    let args = with_absolute_program(&SYSTEM_BIN_DIRS, args)?;
    let pkexec = pkexec().ok_or("installing system-wide needs polkit (pkexec), which isn't installed")?;
    let status = process::command(pkexec).args(&args).status().map_err(|e| format!("couldn't ask for permission ({e})"))?;
    super::root_outcome(status.code())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn os(value: &str) -> OsString {
        OsString::from(value)
    }

    #[test]
    fn the_package_commands_are_the_ones_the_launcher_builds() {
        #[cfg(target_os = "linux")]
        {
            use artcraft_launcher_core::PackageKind;
            assert_eq!(crate::install::linux::install_command(PackageKind::Deb), Some(APT_INSTALL));
        }
        for command in RootCommand::ALL {
            let argv = command.argv();
            let mut args: Vec<&OsStr> = argv.iter().map(OsStr::new).collect();
            args.push(OsStr::new("/downloads/app.deb"));
            let (found, targets) = RootCommand::of(&args).expect("every command is recognized");
            assert_eq!(found, command);
            assert_eq!(targets, vec![OsStr::new("/downloads/app.deb")]);
        }
    }

    #[test]
    fn the_longest_command_claims_the_call() {
        let mut args: Vec<&OsStr> = DNF_INSTALL.iter().map(OsStr::new).collect();
        args.push(OsStr::new("/downloads/app.rpm"));
        assert_eq!(RootCommand::of(&args).map(|(command, _)| command), Some(RootCommand::DnfInstall));
    }

    #[test]
    fn a_call_without_targets_is_not_shared() {
        let args: Vec<&OsStr> = APT_INSTALL.iter().map(OsStr::new).collect();
        assert_eq!(RootCommand::of(&args), None);
    }

    #[test]
    fn an_unknown_command_is_not_shared() {
        let args = [OsStr::new("/bin/sh"), OsStr::new("-c"), OsStr::new("id")];
        assert_eq!(RootCommand::of(&args), None);
    }

    #[test]
    fn requests_round_trip() {
        let targets = [os("/downloads/a.deb"), os("/downloads/b.deb")];
        let borrowed: Vec<&OsStr> = targets.iter().map(OsString::as_os_str).collect();
        let payload = encode(RootCommand::AptInstall, &borrowed).expect("a small request");
        let request = decode(&payload).expect("the helper reads it back");
        assert_eq!(request.command, RootCommand::AptInstall);
        assert_eq!(request.targets, targets);
    }

    #[test]
    fn malformed_requests_are_refused() {
        assert!(decode(&[]).is_err());
        assert!(decode(&[99]).is_err());
        assert!(decode(&[0, 0, 0, 0, 0]).is_err(), "no targets");
        // A target that claims to be longer than the request.
        assert!(decode(&[0, 0, 0, 0, 1, 0, 0, 0, 9, b'a']).is_err());
        // Data after the last target.
        let mut payload = encode(RootCommand::AptRemove, &[OsStr::new("photocraft")]).expect("a small request");
        payload.push(0);
        assert!(decode(&payload).is_err());
    }

    #[test]
    fn oversized_requests_are_refused() {
        let big = "a".repeat(MAX_TARGET + 1);
        assert!(encode(RootCommand::AptInstall, &[OsStr::new(&big)]).is_err());
        assert!(encode(RootCommand::AptInstall, &[]).is_err());
    }

    #[test]
    fn package_files_must_be_absolute_and_exist() {
        assert!(check_file(OsStr::new("relative.deb"), None).is_err());
        assert!(check_file(OsStr::new("/no/such/package.deb"), None).is_err());
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("app.deb");
        std::fs::write(&file, b"package").unwrap();
        assert_eq!(check_file(file.as_os_str(), None), Ok(()));
        // The helper only trusts the user who approved the prompt.
        assert!(check_file(file.as_os_str(), Some(u32::MAX)).is_err());
    }

    #[test]
    fn package_names_look_like_names() {
        for name in ["photocraft", "photocraft-bin", "com.storyteller.photocraft", "gcc@12"] {
            assert_eq!(check_name(OsStr::new(name)), Ok(()), "{name}");
        }
        for name in ["", "--option", "a/b", "a b", "a\nb"] {
            assert!(check_name(OsStr::new(name)).is_err(), "{name}");
        }
    }

    #[test]
    fn removal_commands_take_names_and_installs_take_files() {
        assert_eq!(RootCommand::AptInstall.targets(), Targets::Files);
        assert_eq!(RootCommand::PacmanInstall.targets(), Targets::Files);
        assert_eq!(RootCommand::AptRemove.targets(), Targets::Names);
        assert_eq!(RootCommand::FlatpakSystemUninstall.targets(), Targets::Names);
    }
}
