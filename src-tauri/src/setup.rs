use crate::disk;
use crate::shell::run;
use crate::state::*;
use flate2::read::GzDecoder;
use futures_util::StreamExt;
use reqwest::header::{HeaderMap, CONTENT_RANGE, RANGE};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};
use std::time::Duration;
use tauri::{AppHandle, Emitter};
use tokio::fs;
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::process::Command;
use tokio::time::{sleep, Instant};

// ── Constants ───────────────────────────────────────────────────────

const INSTALL_MANIFEST: &str = "stella-install.json";
const RELEASE_MANIFEST: &str = "stella-release.json";
const LAUNCH_SCRIPT_WIN: &str = "launch.cmd";
const LAUNCH_SCRIPT_UNIX: &str = "launch.sh";
const ENV_FILE_NAME: &str = ".env.local";
// A cold clone install temporarily holds the checked-out app, Bun's package
// cache, node_modules, Electron, and release-pinned native artifacts together.
// Keep headroom for filesystem metadata and installer caches.
const ESTIMATED_INSTALL_BYTES: u64 = 6 * 1024 * 1024 * 1024; // 6 GB
const DEFAULT_ENV_FILE_CONTENTS: &str = "\
VITE_CONVEX_URL=https://benevolent-minnow-586.convex.cloud\n\
VITE_CONVEX_SITE_URL=https://cloud.stella.sh\n\
VITE_SITE_URL=https://stella.sh\n";

const STELLA_GITHUB_REMOTE_URL: &str = "https://github.com/ruuxi/stella";
const DEFAULT_DESKTOP_RELEASE_MANIFEST_URL: &str =
    "https://pub-a319aaada8144dc9be5a83625033769c.r2.dev/desktop/current.json";
const DEFAULT_GIT_RUNTIME_MANIFEST_BASE_URL: &str =
    "https://pub-a319aaada8144dc9be5a83625033769c.r2.dev/git-runtime/versions";
const INSTALL_DIR_NAME: &str = "stella";
const DOWNLOAD_RETRY_ATTEMPTS: usize = 5;
const DOWNLOAD_CONNECT_TIMEOUT: Duration = Duration::from_secs(20);
const DOWNLOAD_READ_TIMEOUT: Duration = Duration::from_secs(30);
const WINDOWS_REMOVE_RETRY_TIMEOUT: Duration = Duration::from_secs(15);
const WINDOWS_REMOVE_RETRY_POLL: Duration = Duration::from_millis(250);
const RIPGREP_VERSION: &str = "15.1.0";
const MANAGED_GIT_VERSION: &str = "2.53.0";
const MANAGED_NODE_VERSION: &str = "24.14.1";
const MANAGED_PYTHON_VERSION: &str = "3.12";
const MANAGED_UV_VERSION: &str = "0.11.32";

fn native_helpers_platform_dir() -> &'static str {
    if cfg!(target_os = "windows") {
        "win32"
    } else if cfg!(target_os = "macos") {
        "darwin"
    } else {
        "linux"
    }
}

fn ripgrep_platform_asset() -> Option<(&'static str, &'static str)> {
    if cfg!(all(target_os = "windows", target_arch = "x86_64")) {
        Some(("x86_64-pc-windows-msvc", "zip"))
    } else if cfg!(all(target_os = "windows", target_arch = "aarch64")) {
        Some(("aarch64-pc-windows-msvc", "zip"))
    } else if cfg!(all(target_os = "windows", target_arch = "x86")) {
        Some(("i686-pc-windows-msvc", "zip"))
    } else if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        Some(("aarch64-apple-darwin", "tar.gz"))
    } else if cfg!(all(target_os = "macos", target_arch = "x86_64")) {
        Some(("x86_64-apple-darwin", "tar.gz"))
    } else if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
        Some(("aarch64-unknown-linux-gnu", "tar.gz"))
    } else if cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        Some(("x86_64-unknown-linux-musl", "tar.gz"))
    } else {
        None
    }
}

fn ripgrep_executable_name() -> &'static str {
    if cfg!(target_os = "windows") {
        "rg.exe"
    } else {
        "rg"
    }
}

// ── Path helpers ────────────────────────────────────────────────────

fn home_dir() -> PathBuf {
    dirs::home_dir().unwrap_or_else(|| PathBuf::from("."))
}

fn expand_home(p: &str) -> String {
    if p == "~" {
        home_dir().to_string_lossy().to_string()
    } else if let Some(rest) = p.strip_prefix("~/") {
        home_dir().join(rest).to_string_lossy().to_string()
    } else if let Some(rest) = p.strip_prefix("~\\") {
        home_dir().join(rest).to_string_lossy().to_string()
    } else {
        p.to_string()
    }
}

fn norm(p: &str) -> String {
    let expanded = expand_home(p.trim());
    match std::fs::canonicalize(&expanded) {
        Ok(canon) => {
            let s = canon.to_string_lossy().to_string();
            s.strip_prefix(r"\\?\").unwrap_or(&s).to_string()
        }
        Err(_) => {
            let pb = PathBuf::from(&expanded);
            if pb.is_absolute() {
                let s = pb.to_string_lossy().to_string();
                s.strip_prefix(r"\\?\").unwrap_or(&s).to_string()
            } else {
                std::env::current_dir()
                    .unwrap_or_default()
                    .join(&pb)
                    .to_string_lossy()
                    .to_string()
            }
        }
    }
}

fn install_dir_name_matches(path: &Path) -> bool {
    path.file_name()
        .and_then(|value| value.to_str())
        .map(|value| value.eq_ignore_ascii_case(INSTALL_DIR_NAME))
        .unwrap_or(false)
}

fn resolve_install_path(input: &str) -> String {
    let normalized = norm(input);
    let normalized_path = Path::new(&normalized);
    if install_dir_name_matches(normalized_path) || looks_like_stella_install_dir(normalized_path) {
        normalized
    } else {
        norm(
            &PathBuf::from(&normalized)
                .join(INSTALL_DIR_NAME)
                .to_string_lossy(),
        )
    }
}

pub fn browse_directory_for_install_path(install_path: &str) -> String {
    let path = PathBuf::from(install_path);
    if install_dir_name_matches(&path) {
        if let Some(parent) = path.parent() {
            return parent.to_string_lossy().to_string();
        }
    }
    install_path.to_string()
}

fn looks_like_stella_install_dir(path: &Path) -> bool {
    path.join(INSTALL_MANIFEST).is_file()
        || path.join(RELEASE_MANIFEST).is_file()
        || looks_like_stella_source_tree(path)
}

fn looks_like_stella_source_tree(path: &Path) -> bool {
    let package_path = path.join("package.json");
    let Ok(raw) = std::fs::read_to_string(package_path) else {
        return false;
    };
    let Ok(package_json) = serde_json::from_str::<serde_json::Value>(&raw) else {
        return false;
    };
    let is_stella_package = package_json
        .get("name")
        .and_then(|value| value.as_str())
        .is_some_and(|name| name == "stella" || name == "stella-workspace");

    is_stella_package && path.join("desktop").is_dir() && path.join("runtime").is_dir()
}

fn is_directory_empty(path: &Path) -> bool {
    match std::fs::read_dir(path) {
        Ok(mut entries) => entries.next().is_none(),
        Err(_) => false,
    }
}

fn is_partial_launcher_install_dir(path: &Path) -> bool {
    let Ok(entries) = std::fs::read_dir(path) else {
        return false;
    };
    let mut saw_launcher_artifact = false;
    for entry in entries {
        let Ok(entry) = entry else {
            return false;
        };
        let name = entry.file_name();
        let Ok(file_type) = entry.file_type() else {
            return false;
        };
        // Launcher/macOS-owned artifacts left behind by a partial or failed
        // install that are safe to clean up.
        if file_type.is_file()
            && (name == "stella-install.log"
                || name == ".DS_Store"
                || name == ".stella-native-helpers-download.tar.zst"
                || name == ".stella-browser-download")
        {
            saw_launcher_artifact = true;
            continue;
        }
        if file_type.is_dir() && name == ".stella-source-clone" {
            saw_launcher_artifact = true;
            continue;
        }
        return false;
    }
    saw_launcher_artifact
}

pub fn is_uninstallable_install_path(install_path: &str) -> bool {
    let path = Path::new(install_path);
    path.is_dir() && (looks_like_stella_install_dir(path) || is_partial_launcher_install_dir(path))
}

fn manifest_of(d: &str) -> PathBuf {
    Path::new(d).join(INSTALL_MANIFEST)
}
fn release_manifest_of(d: &str) -> PathBuf {
    Path::new(d).join(RELEASE_MANIFEST)
}
fn desktop_dir_of(d: &str) -> PathBuf {
    Path::new(d).join("desktop")
}
fn package_json_of(d: &str) -> PathBuf {
    Path::new(d).join("package.json")
}
fn node_modules_of(d: &str) -> PathBuf {
    Path::new(d).join("node_modules")
}
fn electron_dist_dir_of(d: &str) -> PathBuf {
    node_modules_of(d).join("electron").join("dist")
}
fn bun_executable_of() -> PathBuf {
    if cfg!(target_os = "windows") {
        home_dir().join(".bun").join("bin").join("bun.exe")
    } else {
        home_dir().join(".bun").join("bin").join("bun")
    }
}
fn bun_bin_dir() -> PathBuf {
    home_dir().join(".bun").join("bin")
}
fn stella_private_bin_dir() -> PathBuf {
    stella_data_dir().join("bin")
}
fn stella_runtimes_dir() -> PathBuf {
    stella_data_dir().join("runtimes")
}
fn managed_node_dir() -> PathBuf {
    stella_runtimes_dir()
        .join("node")
        .join(MANAGED_NODE_VERSION)
}
fn managed_node_bin_dir() -> PathBuf {
    if cfg!(target_os = "windows") {
        managed_node_dir()
    } else {
        managed_node_dir().join("bin")
    }
}
fn managed_node_binary() -> PathBuf {
    managed_node_bin_dir().join(if cfg!(target_os = "windows") {
        "node.exe"
    } else {
        "node"
    })
}
fn managed_uv_binary() -> PathBuf {
    stella_private_bin_dir().join(if cfg!(target_os = "windows") {
        "uv.exe"
    } else {
        "uv"
    })
}
fn managed_python_install_dir() -> PathBuf {
    stella_runtimes_dir().join("python")
}
fn python_command_names() -> &'static [&'static str] {
    if cfg!(target_os = "windows") {
        &["python.exe", "python3.exe", "python"]
    } else {
        &["python3", "python"]
    }
}
fn ripgrep_private_binary_path() -> PathBuf {
    stella_private_bin_dir().join(ripgrep_executable_name())
}
fn path_separator() -> &'static str {
    if cfg!(target_os = "windows") {
        ";"
    } else {
        ":"
    }
}
fn prepend_path_entry(entry: &Path, existing_path: &str) -> String {
    let entry = entry.to_string_lossy();
    if existing_path.is_empty() {
        entry.to_string()
    } else {
        format!("{entry}{}{existing_path}", path_separator())
    }
}

fn executable_on_path(command: &str) -> Option<PathBuf> {
    let candidate = Path::new(command);
    if candidate.components().count() > 1 && candidate.is_file() {
        return Some(candidate.to_path_buf());
    }

    let path_value = std::env::var_os("PATH")?;
    #[cfg(target_os = "windows")]
    let extensions = {
        let configured =
            std::env::var("PATHEXT").unwrap_or_else(|_| ".COM;.EXE;.BAT;.CMD".to_string());
        configured
            .split(';')
            .filter(|value| !value.is_empty())
            .map(|value| value.to_ascii_lowercase())
            .collect::<Vec<_>>()
    };

    for directory in std::env::split_paths(&path_value) {
        let direct = directory.join(command);
        if direct.is_file() {
            return Some(direct);
        }
        #[cfg(target_os = "windows")]
        if Path::new(command).extension().is_none() {
            for extension in &extensions {
                let with_extension = directory.join(format!("{command}{extension}"));
                if with_extension.is_file() {
                    return Some(with_extension);
                }
            }
        }
    }
    None
}

fn command_succeeds(binary: &Path, args: &[&str]) -> bool {
    command_output(binary, args)
        .map(|output| output.status.success())
        .unwrap_or(false)
}

fn command_output(binary: &Path, args: &[&str]) -> Option<std::process::Output> {
    let mut command = std::process::Command::new(binary);
    command.args(args);
    #[cfg(target_os = "windows")]
    {
        use std::os::windows::process::CommandExt as _;
        command.creation_flags(0x08000000);
    }
    command.output().ok()
}

fn usable_executable_on_path(command: &str, args: &[&str]) -> Option<PathBuf> {
    executable_on_path(command).filter(|binary| command_succeeds(binary, args))
}
fn mac_screen_capture_permissions_dir_of(d: &str) -> PathBuf {
    node_modules_of(d).join("mac-screen-capture-permissions")
}
fn mac_screen_capture_permissions_binary_of(d: &str) -> PathBuf {
    mac_screen_capture_permissions_dir_of(d)
        .join("build")
        .join("Release")
        .join("screencapturepermissions.node")
}
fn launch_script_name() -> &'static str {
    if cfg!(target_os = "windows") {
        LAUNCH_SCRIPT_WIN
    } else {
        LAUNCH_SCRIPT_UNIX
    }
}
fn launch_script_of(d: &str) -> PathBuf {
    Path::new(d).join(launch_script_name())
}

fn desktop_launch_command(low_resource_mode: bool) -> Vec<String> {
    if low_resource_mode {
        vec![
            "bun".into(),
            "run".into(),
            "electron:dev:low-resource".into(),
        ]
    } else {
        vec!["bun".into(), "run".into(), "electron:dev".into()]
    }
}

fn desktop_launch_command_line(low_resource_mode: bool) -> &'static str {
    if low_resource_mode {
        "bun run electron:dev:low-resource"
    } else {
        "bun run electron:dev"
    }
}
fn env_file_of(d: &str) -> PathBuf {
    desktop_dir_of(d).join(ENV_FILE_NAME)
}
fn parakeet_cache_dir_of(d: &str) -> PathBuf {
    desktop_dir_of(d).join("resources").join("parakeet")
}
fn parakeet_helper_of(d: &str) -> PathBuf {
    desktop_dir_of(d)
        .join("native")
        .join("out")
        .join("darwin")
        .join("parakeet_transcriber")
}

// parakeet.cpp local dictation (Windows + Intel macOS). The CoreML helper above
// covers Apple Silicon. Keep these in sync with desktop/electron/dictation/
// local-parakeet.ts (model file, URL, sha256, size).
const PARAKEET_CPP_MODEL_FILE: &str = "tdt-0.6b-v3-q8_0.gguf";
const PARAKEET_CPP_MODEL_URL: &str =
    "https://huggingface.co/mudler/parakeet-cpp-gguf/resolve/main/tdt-0.6b-v3-q8_0.gguf";
const PARAKEET_CPP_MODEL_SHA256: &str =
    "4d69a4a6683f4f2d952bad794c1357ca6eb628027695b4699c5a9ad4cd07d757";
const PARAKEET_CPP_MODEL_SIZE: u64 = 940_663_680;

fn parakeet_cpp_supported() -> bool {
    cfg!(all(target_os = "windows", target_arch = "x86_64"))
        || cfg!(all(target_os = "macos", target_arch = "x86_64"))
}
fn parakeet_cpp_helper_of(d: &str) -> PathBuf {
    let name = if cfg!(target_os = "windows") {
        "parakeet_cpp_transcriber.exe"
    } else {
        "parakeet_cpp_transcriber"
    };
    native_helpers_dir_of(d).join(name)
}
fn parakeet_cpp_model_dir_of(d: &str) -> PathBuf {
    desktop_dir_of(d).join("resources").join("parakeet-cpp")
}
fn parakeet_cpp_model_path_of(d: &str) -> PathBuf {
    parakeet_cpp_model_dir_of(d).join(PARAKEET_CPP_MODEL_FILE)
}
async fn parakeet_cpp_model_present(target: &Path) -> bool {
    match fs::metadata(target).await {
        Ok(meta) => meta.len() == PARAKEET_CPP_MODEL_SIZE,
        Err(_) => false,
    }
}
fn git_bin_of_root(root: &Path) -> PathBuf {
    if cfg!(target_os = "windows") {
        root.join("cmd").join("git.exe")
    } else {
        root.join("bin").join("git")
    }
}
fn managed_git_win32_subfolder() -> &'static str {
    if cfg!(all(target_os = "windows", target_arch = "x86_64")) {
        "mingw64"
    } else if cfg!(all(target_os = "windows", target_arch = "aarch64")) {
        "clangarm64"
    } else {
        "mingw32"
    }
}
fn git_bash_of_root(root: &Path) -> PathBuf {
    if cfg!(target_os = "windows") {
        root.join("usr").join("bin").join("bash.exe")
    } else {
        root.join("bin").join("bash")
    }
}
fn git_exec_path_of_root(root: &Path) -> PathBuf {
    if cfg!(target_os = "windows") {
        root.join(managed_git_win32_subfolder())
            .join("libexec")
            .join("git-core")
    } else {
        root.join("libexec").join("git-core")
    }
}

#[derive(Debug, Clone)]
struct GitRuntime {
    bin: PathBuf,
    env: HashMap<String, String>,
}

fn private_git_env(git_root: &Path) -> HashMap<String, String> {
    let mut env = HashMap::new();
    let git_root_str = git_root.to_string_lossy().to_string();
    let mut launch_path =
        prepend_path_entry(&bun_bin_dir(), &std::env::var("PATH").unwrap_or_default());
    launch_path = prepend_path_entry(&stella_private_bin_dir(), &launch_path);
    env.insert("LOCAL_GIT_DIRECTORY".into(), git_root_str.clone());
    env.insert(
        "STELLA_GIT_BIN".into(),
        git_bin_of_root(git_root).to_string_lossy().to_string(),
    );
    env.insert(
        "GIT_EXEC_PATH".into(),
        git_exec_path_of_root(git_root)
            .to_string_lossy()
            .to_string(),
    );

    if cfg!(target_os = "windows") {
        let mingw_root = git_root.join(managed_git_win32_subfolder());
        let path_prefix = format!(
            "{};{}",
            mingw_root.join("bin").to_string_lossy(),
            git_root.join("usr").join("bin").to_string_lossy()
        );
        env.insert("PATH".into(), format!("{path_prefix};{launch_path}"));
        env.insert(
            "STELLA_GIT_BASH".into(),
            git_bash_of_root(git_root).to_string_lossy().to_string(),
        );
    } else {
        env.insert("PATH".into(), format!("{git_root_str}/bin:{launch_path}"));
        env.insert(
            "GIT_CONFIG_SYSTEM".into(),
            git_root
                .join("etc")
                .join("gitconfig")
                .to_string_lossy()
                .to_string(),
        );
        env.insert(
            "GIT_TEMPLATE_DIR".into(),
            git_root
                .join("share")
                .join("git-core")
                .join("templates")
                .to_string_lossy()
                .to_string(),
        );
    }
    env
}

fn system_git_bash(git_bin: &Path) -> Option<PathBuf> {
    if !cfg!(target_os = "windows") {
        return None;
    }
    let root = git_bin.parent()?.parent()?;
    [
        root.join("bin").join("bash.exe"),
        root.join("usr").join("bin").join("bash.exe"),
    ]
    .into_iter()
    .find(|candidate| candidate.is_file() && command_succeeds(candidate, &["--version"]))
}

fn system_git_runtime() -> Option<GitRuntime> {
    let bin = usable_executable_on_path(
        if cfg!(target_os = "windows") {
            "git.exe"
        } else {
            "git"
        },
        &["--version"],
    )?;
    let mut env = HashMap::new();
    env.insert("STELLA_GIT_BIN".into(), bin.to_string_lossy().to_string());
    if cfg!(target_os = "windows") {
        let bash = system_git_bash(&bin)?;
        env.insert("STELLA_GIT_BASH".into(), bash.to_string_lossy().to_string());
    }
    Some(GitRuntime { bin, env })
}

fn managed_git_runtime() -> Option<GitRuntime> {
    let root = managed_git_root();
    let bin = git_bin_of_root(&root);
    if !bin.is_file() || !command_succeeds(&bin, &["--version"]) {
        return None;
    }
    Some(GitRuntime {
        bin,
        env: private_git_env(&root),
    })
}

fn available_git_runtime() -> Option<GitRuntime> {
    system_git_runtime().or_else(managed_git_runtime)
}

fn node_version_is_usable(binary: &Path) -> bool {
    let Some(output) = command_output(binary, &["--version"]) else {
        return false;
    };
    if !output.status.success() {
        return false;
    }
    let version = String::from_utf8_lossy(&output.stdout);
    let mut parts = version.trim().trim_start_matches('v').split('.');
    let Some(major) = parts.next().and_then(|value| value.parse::<u32>().ok()) else {
        return false;
    };
    let minor = parts
        .next()
        .and_then(|value| value.parse::<u32>().ok())
        .unwrap_or(0);
    major > 20 || (major == 20 && minor >= 19)
}

fn system_node_binary() -> Option<PathBuf> {
    let node = executable_on_path(if cfg!(target_os = "windows") {
        "node.exe"
    } else {
        "node"
    })
    .filter(|binary| node_version_is_usable(binary))?;
    let npm_name = if cfg!(target_os = "windows") {
        "npm.cmd"
    } else {
        "npm"
    };
    let npx_name = if cfg!(target_os = "windows") {
        "npx.cmd"
    } else {
        "npx"
    };
    usable_executable_on_path(npm_name, &["--version"])?;
    usable_executable_on_path(npx_name, &["--version"])?;
    Some(node)
}

fn managed_node_is_usable() -> bool {
    if !node_version_is_usable(&managed_node_binary()) {
        return false;
    }
    let npm = managed_node_bin_dir().join(if cfg!(target_os = "windows") {
        "npm.cmd"
    } else {
        "npm"
    });
    let npx = managed_node_bin_dir().join(if cfg!(target_os = "windows") {
        "npx.cmd"
    } else {
        "npx"
    });
    npm.is_file() && npx.is_file()
}

fn available_node_binary() -> Option<PathBuf> {
    system_node_binary().or_else(|| {
        let managed = managed_node_binary();
        managed_node_is_usable().then_some(managed)
    })
}

fn python_version_is_usable(binary: &Path) -> bool {
    if cfg!(target_os = "windows")
        && binary
            .to_string_lossy()
            .to_ascii_lowercase()
            .contains("\\windowsapps\\")
    {
        // The Microsoft Store app-execution alias can open UI when invoked;
        // it is not an installed interpreter and must not count as the fast path.
        return false;
    }
    command_succeeds(
        binary,
        &[
            "-c",
            "import sys; raise SystemExit(0 if sys.version_info >= (3, 11) else 1)",
        ],
    )
}

fn available_python_binary() -> Option<PathBuf> {
    python_command_names()
        .iter()
        .find_map(|name| executable_on_path(name).filter(|path| python_version_is_usable(path)))
        .or_else(|| {
            python_command_names().iter().find_map(|name| {
                let candidate = stella_private_bin_dir().join(name);
                python_version_is_usable(&candidate).then_some(candidate)
            })
        })
}

pub fn runtime_launch_env(_install_dir: &str) -> HashMap<String, String> {
    let mut launch_path =
        prepend_path_entry(&bun_bin_dir(), &std::env::var("PATH").unwrap_or_default());
    launch_path = prepend_path_entry(&stella_private_bin_dir(), &launch_path);
    let mut env = HashMap::new();
    env.insert(
        "STELLA_DATA_DIR".into(),
        stella_data_dir().to_string_lossy().to_string(),
    );
    if let Some(git) = available_git_runtime() {
        if let Some(git_path) = git.env.get("PATH") {
            launch_path = git_path.clone();
        } else if let Some(parent) = git.bin.parent() {
            launch_path = prepend_path_entry(parent, &launch_path);
        }
        env.extend(git.env);
    }
    if let Some(node) = available_node_binary() {
        if let Some(parent) = node.parent() {
            launch_path = prepend_path_entry(parent, &launch_path);
        }
        env.insert("STELLA_NODE_BIN".into(), node.to_string_lossy().to_string());
        env.insert("STELLA_NODE_IS_ELECTRON".into(), "0".into());
    }
    if let Some(python) = available_python_binary() {
        if let Some(parent) = python.parent() {
            launch_path = prepend_path_entry(parent, &launch_path);
        }
        env.insert(
            "STELLA_PYTHON_BIN".into(),
            python.to_string_lossy().to_string(),
        );
    }
    if let Some(uv) = usable_executable_on_path(
        if cfg!(target_os = "windows") {
            "uv.exe"
        } else {
            "uv"
        },
        &["--version"],
    )
    .or_else(|| {
        let managed = managed_uv_binary();
        command_succeeds(&managed, &["--version"]).then_some(managed)
    }) {
        env.insert("STELLA_UV_BIN".into(), uv.to_string_lossy().to_string());
    }
    launch_path = prepend_path_entry(&stella_private_bin_dir(), &launch_path);
    env.insert("PATH".into(), launch_path);
    env
}

// ── Validation ──────────────────────────────────────────────────────

fn location_error(p: &str) -> Option<String> {
    let trimmed = p.trim();
    if trimmed.is_empty() {
        return Some("Choose where Stella should be installed.".into());
    }
    let pb = PathBuf::from(trimmed);
    if !pb.is_absolute() {
        return Some("Install location must be an absolute path.".into());
    }
    if let Ok(metadata) = std::fs::metadata(&pb) {
        if !metadata.is_dir() {
            return Some("Install location must be a folder.".into());
        }
        if !looks_like_stella_install_dir(&pb)
            && !is_directory_empty(&pb)
            && !is_partial_launcher_install_dir(&pb)
        {
            return Some(format!(
                "Stella needs its own `{INSTALL_DIR_NAME}` folder. Choose a parent folder or an existing Stella install."
            ));
        }
    }
    None
}

// ── Helpers ─────────────────────────────────────────────────────────

async fn path_exists(p: &Path) -> bool {
    fs::metadata(p).await.is_ok()
}

async fn path_exists_str(p: &str) -> bool {
    path_exists(Path::new(p)).await
}

async fn valid_install_manifest_exists(install_dir: &str) -> bool {
    let manifest_path = manifest_of(install_dir);
    let Ok(raw) = fs::read_to_string(&manifest_path).await else {
        return false;
    };
    serde_json::from_str::<Manifest>(&raw).is_ok()
}

async fn write_install_manifest_atomic(
    manifest_path: &Path,
    manifest: &Manifest,
) -> Result<(), String> {
    let json = serde_json::to_string_pretty(manifest)
        .map_err(|e| format!("Failed to serialize install manifest: {e}"))?;
    let _: Manifest = serde_json::from_str(&json)
        .map_err(|e| format!("Serialized install manifest was invalid: {e}"))?;
    let tmp_path = manifest_path.with_file_name(format!(
        ".{}.{}.tmp",
        manifest_path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or(INSTALL_MANIFEST),
        std::process::id()
    ));
    fs::write(&tmp_path, json)
        .await
        .map_err(|e| format!("Failed to write temporary install manifest: {e}"))?;
    match fs::rename(&tmp_path, manifest_path).await {
        Ok(()) => Ok(()),
        Err(e) => {
            let _ = fs::remove_file(&tmp_path).await;
            Err(format!("Failed to persist install manifest: {e}"))
        }
    }
}

#[derive(Debug, Clone, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct DesktopDownloadManifest {
    schema_version: u32,
    tag: String,
    commit: String,
    platforms: HashMap<String, DesktopPlatformRelease>,
}

#[derive(Debug, Clone, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct DesktopPlatformRelease {
    artifact_refs: Vec<DesktopArtifactRef>,
}

#[derive(Debug, Clone, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct DesktopArtifactRef {
    kind: String,
    platform: String,
    #[serde(default)]
    manifest_url: Option<String>,
    #[serde(default)]
    manifest_sha: Option<String>,
    #[serde(default)]
    commit: Option<String>,
    #[serde(default)]
    built_at: Option<String>,
    asset: DesktopArtifactAsset,
}

#[derive(Debug, Clone, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct DesktopArtifactAsset {
    url: String,
    sha256: String,
    #[serde(alias = "size")]
    size_bytes: u64,
}

#[derive(Debug, Clone)]
struct ResolvedDesktopRelease {
    tag: String,
    commit: String,
    platform: String,
    artifact_refs: Vec<DesktopArtifactRef>,
}

#[derive(Debug, Clone, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct DesktopReleaseManifest {
    schema_version: u32,
    tag: String,
    #[serde(default)]
    commit: Option<String>,
    #[allow(dead_code)]
    #[serde(default)]
    files: HashMap<String, ReleaseFileEntry>,
}

#[derive(Debug, Clone, serde::Deserialize)]
struct ReleaseFileEntry {
    #[allow(dead_code)]
    sha256: String,
}

fn desktop_release_manifest_url() -> String {
    std::env::var("STELLA_DESKTOP_RELEASE_MANIFEST_URL")
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| DEFAULT_DESKTOP_RELEASE_MANIFEST_URL.to_string())
}

fn desktop_platform_key() -> &'static str {
    if cfg!(all(target_os = "windows", target_arch = "x86_64")) {
        "win-x64"
    } else if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        "darwin-arm64"
    } else if cfg!(all(target_os = "macos", target_arch = "x86_64")) {
        "darwin-x64"
    } else {
        "linux-x64"
    }
}

#[derive(Debug, Clone, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct ManagedGitAsset {
    file_name: String,
    url: String,
    sha256: String,
    size: u64,
}

#[derive(Debug, Clone, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct ManagedGitManifest {
    schema_version: u32,
    version: String,
    assets: HashMap<String, ManagedGitAsset>,
}

#[derive(Debug, Clone, Copy)]
struct ManagedNodeAsset {
    file_name: &'static str,
    url: &'static str,
    sha256: &'static str,
}

fn managed_node_asset() -> Option<ManagedNodeAsset> {
    if cfg!(all(target_os = "windows", target_arch = "x86_64")) {
        Some(ManagedNodeAsset {
            file_name: "node-v24.14.1-win-x64.zip",
            url: "https://nodejs.org/dist/v24.14.1/node-v24.14.1-win-x64.zip",
            sha256: "6e50ce5498c0cebc20fd39ab3ff5df836ed2f8a31aa093cecad8497cff126d70",
        })
    } else if cfg!(all(target_os = "windows", target_arch = "aarch64")) {
        Some(ManagedNodeAsset {
            file_name: "node-v24.14.1-win-arm64.zip",
            url: "https://nodejs.org/dist/v24.14.1/node-v24.14.1-win-arm64.zip",
            sha256: "a7b7c68490e4a8cde1921fe5a0cfb3001d53f9c839e416903e4f28e727b62f60",
        })
    } else if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        Some(ManagedNodeAsset {
            file_name: "node-v24.14.1-darwin-arm64.tar.gz",
            url: "https://nodejs.org/dist/v24.14.1/node-v24.14.1-darwin-arm64.tar.gz",
            sha256: "25495ff85bd89e2d8a24d88566d7e2f827c6b0d3d872b2cebf75371f93fcb1fe",
        })
    } else if cfg!(all(target_os = "macos", target_arch = "x86_64")) {
        Some(ManagedNodeAsset {
            file_name: "node-v24.14.1-darwin-x64.tar.gz",
            url: "https://nodejs.org/dist/v24.14.1/node-v24.14.1-darwin-x64.tar.gz",
            sha256: "2526230ad7d922be82d4fdb1e7ee1e84303e133e3b4b0ec4c2897ab31de0253d",
        })
    } else if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
        Some(ManagedNodeAsset {
            file_name: "node-v24.14.1-linux-arm64.tar.gz",
            url: "https://nodejs.org/dist/v24.14.1/node-v24.14.1-linux-arm64.tar.gz",
            sha256: "734ff04fa7f8ed2e8a78d40cacf5ac3fc4515dac2858757cbab313eb483ba8a2",
        })
    } else if cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        Some(ManagedNodeAsset {
            file_name: "node-v24.14.1-linux-x64.tar.gz",
            url: "https://nodejs.org/dist/v24.14.1/node-v24.14.1-linux-x64.tar.gz",
            sha256: "ace9fa104992ed0829642629c46ca7bd7fd6e76278cb96c958c4b387d29658ea",
        })
    } else {
        None
    }
}

fn managed_node_cache_dir() -> PathBuf {
    stella_data_dir()
        .join("cache")
        .join("launcher")
        .join("node")
        .join(MANAGED_NODE_VERSION)
}

fn managed_node_archive_path() -> Result<PathBuf, String> {
    managed_node_asset()
        .map(|asset| managed_node_cache_dir().join(asset.file_name))
        .ok_or_else(|| {
            format!(
                "Stella's managed Node runtime is not available for {}/{}.",
                std::env::consts::OS,
                std::env::consts::ARCH
            )
        })
}

fn managed_runtime_platform_key() -> Option<&'static str> {
    if cfg!(all(target_os = "windows", target_arch = "x86_64")) {
        Some("win-x64")
    } else if cfg!(all(target_os = "windows", target_arch = "aarch64")) {
        Some("win-arm64")
    } else if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        Some("darwin-arm64")
    } else if cfg!(all(target_os = "macos", target_arch = "x86_64")) {
        Some("darwin-x64")
    } else if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
        Some("linux-arm64")
    } else if cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        Some("linux-x64")
    } else {
        None
    }
}

fn git_runtime_manifest_url() -> String {
    std::env::var("STELLA_GIT_RUNTIME_MANIFEST_URL")
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| {
            format!("{DEFAULT_GIT_RUNTIME_MANIFEST_BASE_URL}/{MANAGED_GIT_VERSION}/manifest.json")
        })
}

fn resolve_managed_git_asset(manifest: ManagedGitManifest) -> Result<ManagedGitAsset, String> {
    if manifest.schema_version != 1 {
        return Err("Git runtime manifest schema is not supported.".into());
    }
    if manifest.version != MANAGED_GIT_VERSION {
        return Err(format!(
            "Git runtime manifest version did not match {MANAGED_GIT_VERSION}."
        ));
    }
    let platform = managed_runtime_platform_key().ok_or_else(|| {
        format!(
            "Stella's private Git runtime is not available for {}/{}.",
            std::env::consts::OS,
            std::env::consts::ARCH
        )
    })?;
    let mut asset = manifest
        .assets
        .get(platform)
        .cloned()
        .ok_or_else(|| format!("Git runtime manifest did not include platform {platform}."))?;
    let expected_file_name = format!("stella-git-{platform}.tar.gz");
    if asset.file_name != expected_file_name
        || Path::new(&asset.file_name)
            .file_name()
            .and_then(|name| name.to_str())
            != Some(asset.file_name.as_str())
    {
        return Err("Git runtime manifest contained an invalid archive name.".into());
    }
    if !asset.url.starts_with("https://") {
        return Err("Git runtime manifest contained an invalid artifact URL.".into());
    }
    asset.sha256 = normalize_sha256(&asset.sha256)
        .ok_or_else(|| "Git runtime manifest contained an invalid checksum.".to_string())?;
    if asset.size == 0 {
        return Err("Git runtime manifest contained an invalid artifact size.".into());
    }
    Ok(asset)
}

fn managed_git_dir() -> PathBuf {
    stella_runtimes_dir()
        .join("git")
        .join(MANAGED_GIT_VERSION)
        .join(managed_runtime_platform_key().unwrap_or("unsupported"))
}

fn managed_git_root() -> PathBuf {
    managed_git_dir().join("git")
}

fn managed_git_archive_path(asset: &ManagedGitAsset) -> PathBuf {
    managed_git_dir().join(&asset.file_name)
}

fn source_clone_dir_of(install_dir: &str) -> PathBuf {
    Path::new(install_dir).join(".stella-source-clone")
}

fn native_helpers_dir_of(install_dir: &str) -> PathBuf {
    desktop_dir_of(install_dir)
        .join("native")
        .join("out")
        .join(native_helpers_platform_dir())
}

fn normalize_sha256(value: &str) -> Option<String> {
    value.split_whitespace().find_map(|part| {
        let candidate = part
            .get(..7)
            .filter(|prefix| prefix.eq_ignore_ascii_case("sha256:"))
            .map(|_| &part[7..])
            .unwrap_or(part);
        (candidate.len() == 64 && candidate.chars().all(|char| char.is_ascii_hexdigit()))
            .then(|| candidate.to_ascii_lowercase())
    })
}

// ── Settings persistence ────────────────────────────────────────────

async fn read_settings(ctx: &InstallerContext) -> Settings {
    match fs::read_to_string(&ctx.settings_file_path).await {
        Ok(content) => serde_json::from_str(&content).unwrap_or_default(),
        Err(_) => Settings::default(),
    }
}

async fn write_settings(ctx: &InstallerContext, state: &InstallerState) {
    let existing = read_settings(ctx).await;
    let settings = Settings {
        install_path: Some(state.install_path.clone()),
        installed_path: if state.installed {
            Some(state.install_path.clone())
        } else {
            existing.installed_path
        },
        run_after_install: Some(state.run_after_install),
        low_resource_mode: state.low_resource_mode,
    };
    if let Some(parent) = ctx.settings_file_path.parent() {
        let _ = fs::create_dir_all(parent).await;
    }
    let json = serde_json::to_string_pretty(&settings).unwrap_or_default();
    let _ = fs::write(&ctx.settings_file_path, json).await;
}

// ── Launch script ───────────────────────────────────────────────────

async fn write_launch_script(install_dir: &str, low_resource_mode: bool) -> String {
    let script_path = launch_script_of(install_dir);
    let launch_env = runtime_launch_env(install_dir);
    let launch_command = desktop_launch_command_line(low_resource_mode);

    if cfg!(target_os = "windows") {
        let mut content = format!("@echo off\r\ncd /d \"{install_dir}\"\r\n");
        if let Some(git_path) = launch_env.get("STELLA_GIT_BIN") {
            content.push_str(&format!("set \"STELLA_GIT_BIN={git_path}\"\r\n"));
        }
        if let Some(bash_path) = launch_env.get("STELLA_GIT_BASH") {
            content.push_str(&format!("set \"STELLA_GIT_BASH={bash_path}\"\r\n"));
        }
        if let Some(git_dir) = launch_env.get("LOCAL_GIT_DIRECTORY") {
            content.push_str(&format!("set \"LOCAL_GIT_DIRECTORY={git_dir}\"\r\n"));
        }
        if let Some(git_exec_path) = launch_env.get("GIT_EXEC_PATH") {
            content.push_str(&format!("set \"GIT_EXEC_PATH={git_exec_path}\"\r\n"));
        }
        if let Some(stella_data_dir) = launch_env.get("STELLA_DATA_DIR") {
            content.push_str(&format!("set \"STELLA_DATA_DIR={stella_data_dir}\"\r\n"));
        }
        for key in [
            "STELLA_NODE_BIN",
            "STELLA_NODE_IS_ELECTRON",
            "STELLA_PYTHON_BIN",
            "STELLA_UV_BIN",
        ] {
            if let Some(value) = launch_env.get(key) {
                content.push_str(&format!("set \"{key}={value}\"\r\n"));
            }
        }
        if let Some(path_value) = launch_env.get("PATH") {
            content.push_str(&format!("set \"PATH={path_value}\"\r\n"));
        }
        content.push_str(launch_command);
        content.push_str("\r\n");
        let _ = fs::write(&script_path, content).await;
    } else {
        let mut content = format!("#!/bin/sh\ncd \"{install_dir}\"\n");
        if let Some(git_path) = launch_env.get("STELLA_GIT_BIN") {
            content.push_str(&format!("export STELLA_GIT_BIN=\"{git_path}\"\n"));
        }
        if let Some(bash_path) = launch_env.get("STELLA_GIT_BASH") {
            content.push_str(&format!("export STELLA_GIT_BASH=\"{bash_path}\"\n"));
        }
        if let Some(git_dir) = launch_env.get("LOCAL_GIT_DIRECTORY") {
            content.push_str(&format!("export LOCAL_GIT_DIRECTORY=\"{git_dir}\"\n"));
        }
        if let Some(git_exec_path) = launch_env.get("GIT_EXEC_PATH") {
            content.push_str(&format!("export GIT_EXEC_PATH=\"{git_exec_path}\"\n"));
        }
        if let Some(git_config_system) = launch_env.get("GIT_CONFIG_SYSTEM") {
            content.push_str(&format!(
                "export GIT_CONFIG_SYSTEM=\"{git_config_system}\"\n"
            ));
        }
        if let Some(git_template_dir) = launch_env.get("GIT_TEMPLATE_DIR") {
            content.push_str(&format!("export GIT_TEMPLATE_DIR=\"{git_template_dir}\"\n"));
        }
        if let Some(stella_data_dir) = launch_env.get("STELLA_DATA_DIR") {
            content.push_str(&format!("export STELLA_DATA_DIR=\"{stella_data_dir}\"\n"));
        }
        for key in [
            "STELLA_NODE_BIN",
            "STELLA_NODE_IS_ELECTRON",
            "STELLA_PYTHON_BIN",
            "STELLA_UV_BIN",
        ] {
            if let Some(value) = launch_env.get(key) {
                content.push_str(&format!("export {key}=\"{value}\"\n"));
            }
        }
        if let Some(path_value) = launch_env.get("PATH") {
            content.push_str(&format!("export PATH=\"{path_value}\"\n"));
        }
        content.push_str("exec ");
        content.push_str(launch_command);
        content.push('\n');
        let _ = fs::write(&script_path, &content).await;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if let Ok(meta) = fs::metadata(&script_path).await {
                let mut perms = meta.permissions();
                perms.set_mode(0o755);
                let _ = fs::set_permissions(&script_path, perms).await;
            }
        }
    }

    script_path.to_string_lossy().to_string()
}

async fn write_default_env_file(install_dir: &str) -> Result<(), String> {
    fs::write(env_file_of(install_dir), DEFAULT_ENV_FILE_CONTENTS)
        .await
        .map_err(|e| format!("Failed to write {ENV_FILE_NAME}: {e}"))
}

// ── Windows registry ────────────────────────────────────────────────

const REG_UNINSTALL: &str = r"HKCU\Software\Microsoft\Windows\CurrentVersion\Uninstall\Stella";

async fn write_registry(manifest: &Manifest) {
    if !cfg!(target_os = "windows") {
        return;
    }

    let size_kb = (ESTIMATED_INSTALL_BYTES / 1024).to_string();
    let launcher_exe = std::env::current_exe().ok();
    let display_icon = launcher_exe
        .as_ref()
        .map(|path| path.to_string_lossy().to_string())
        .unwrap_or_else(|| manifest.launch_script.clone());
    let uninstall_string = launcher_exe
        .as_ref()
        .map(|path| {
            crate::bootstrap::windows_uninstall_command(
                path,
                Some(Path::new(&manifest.install_path)),
            )
        })
        .unwrap_or_else(|| manifest.launch_script.clone());
    let entries = vec![
        ("DisplayName", "REG_SZ", "Stella".to_string()),
        ("DisplayVersion", "REG_SZ", manifest.version.clone()),
        ("Publisher", "REG_SZ", "Stella".to_string()),
        ("InstallLocation", "REG_SZ", manifest.install_path.clone()),
        ("DisplayIcon", "REG_SZ", display_icon),
        ("UninstallString", "REG_SZ", uninstall_string),
        ("NoModify", "REG_DWORD", "1".to_string()),
        ("NoRepair", "REG_DWORD", "1".to_string()),
        ("EstimatedSize", "REG_DWORD", size_kb),
    ];

    for (name, reg_type, data) in entries {
        run(
            &[
                "reg",
                "add",
                REG_UNINSTALL,
                "/v",
                name,
                "/t",
                reg_type,
                "/d",
                &data,
                "/f",
            ],
            None,
        )
        .await;
    }
}

async fn remove_registry() {
    if cfg!(target_os = "windows") {
        run(&["reg", "delete", REG_UNINSTALL, "/f"], None).await;
    }
}

// ── Bun ─────────────────────────────────────────────────────────────

async fn bun_on_path() -> bool {
    if run(&["bun", "--version"], None).await.ok {
        return true;
    }

    // GUI apps don't inherit shell startup files, so keep the launcher process
    // PATH aligned with the Bun install location used by launch scripts.
    let bun_bin = bun_executable_of();

    if path_exists(&bun_bin).await {
        if let Some(bin_dir) = bun_bin.parent() {
            let current_path = std::env::var("PATH").unwrap_or_default();
            std::env::set_var("PATH", prepend_path_entry(bin_dir, &current_path));
            return run(&["bun", "--version"], None).await.ok;
        }
    }

    false
}

async fn install_bun_globally() -> bool {
    if cfg!(target_os = "windows") {
        let result = run(
            &[
                "powershell",
                "-NoProfile",
                "-NonInteractive",
                "-Command",
                "irm https://bun.sh/install.ps1 | iex",
            ],
            None,
        )
        .await;
        if !result.ok {
            return false;
        }
    } else {
        let result = run(
            &["bash", "-lc", "curl -fsSL https://bun.sh/install | bash"],
            None,
        )
        .await;
        if !result.ok {
            return false;
        }
    }

    bun_on_path().await
}

fn format_bytes_compact(bytes: u64) -> String {
    const KB: f64 = 1024.0;
    const MB: f64 = KB * 1024.0;
    const GB: f64 = MB * 1024.0;
    let value = bytes as f64;
    if value >= GB {
        format!("{:.1} GB", value / GB)
    } else if value >= MB {
        format!("{:.1} MB", value / MB)
    } else if value >= KB {
        format!("{:.1} KB", value / KB)
    } else {
        format!("{bytes} B")
    }
}

fn set_step_progress(
    state: &mut InstallerState,
    app: &AppHandle,
    id: &SetupStepId,
    detail: impl Into<String>,
    progress: Option<f64>,
) {
    if let Some(step) = state.steps.iter_mut().find(|s| &s.id == id) {
        step.detail = Some(detail.into());
        step.progress = progress.map(|value| value.clamp(0.0, 1.0));
    }
    emit_state_fast(state, app);
}

async fn install_payload_dependencies(
    install_dir: &str,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<(), String> {
    let dir = Some(Path::new(install_dir));
    let result = run_bun_install_with_progress(install_dir, dir, state, app).await;
    if result.ok {
        ensure_electron_binary_installed(install_dir, state, app).await?;
        prewarm_vite_dep_cache(install_dir, state, app).await;
        // This addon is optional at runtime: the desktop app already falls back to
        // Electron/native-helper permission checks when the native module is missing.
        if let Err(err) = ensure_mac_screen_capture_permissions_built(install_dir).await {
            log_install(
                install_dir,
                &format!(
                    "Optional mac-screen-capture-permissions build failed; continuing with fallbacks: {err}"
                ),
            )
            .await;
        }
        Ok(())
    } else {
        let mut output_sections = Vec::new();
        if !result.stderr.is_empty() {
            output_sections.push(format!("stderr:\n{}", result.stderr));
        }
        if !result.stdout.is_empty() {
            output_sections.push(format!("stdout:\n{}", result.stdout));
        }

        if !output_sections.is_empty() {
            log_install(
                install_dir,
                &format!(
                    "bun install --frozen-lockfile failed\n{}",
                    output_sections.join("\n\n")
                ),
            )
            .await;
        }

        let summary = if !result.stderr.is_empty() {
            result.stderr
        } else if !result.stdout.is_empty() {
            result.stdout
        } else {
            "bun install failed.".into()
        };

        Err(format!("bun install failed: {summary}"))
    }
}

/// Pre-warms Vite's dependency-optimizer cache (`node_modules/.vite`) so the
/// first launch skips the cold prebundle of the heavy renderer deps. Must run
/// here on the user's machine rather than in release CI: Vite's dep hash
/// covers the absolute install path, so a CI-baked cache is discarded as
/// stale. Non-fatal — a failed prewarm just means the first launch pays the
/// prebundle like before (older payloads without the `deps:prewarm` script
/// land here too).
async fn prewarm_vite_dep_cache(install_dir: &str, state: &mut InstallerState, app: &AppHandle) {
    set_step_progress(
        state,
        app,
        &SetupStepId::Payload,
        "Optimizing for first launch",
        Some(0.98),
    );
    log_install(install_dir, "Pre-warming Vite dependency cache").await;

    let result = run(
        &["bun", "run", "deps:prewarm"],
        Some(Path::new(install_dir)),
    )
    .await;
    if result.ok {
        log_install(install_dir, "Vite dependency cache ready").await;
    } else {
        let summary = run_failure_summary(&result, "Vite dependency prewarm failed.");
        log_install(
            install_dir,
            &format!("bun run deps:prewarm failed (continuing)\n{summary}"),
        )
        .await;
    }
}

async fn ensure_electron_binary_installed(
    install_dir: &str,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<(), String> {
    if path_exists(&electron_dist_dir_of(install_dir)).await {
        log_install(install_dir, "Electron binary already installed").await;
        return Ok(());
    }

    set_step_progress(
        state,
        app,
        &SetupStepId::Payload,
        "Preparing Electron",
        Some(0.95),
    );
    log_install(install_dir, "Preparing Electron binary").await;

    let result = run(
        &["bun", "./node_modules/electron/install.js"],
        Some(Path::new(install_dir)),
    )
    .await;
    if result.ok {
        return Ok(());
    }

    let summary = run_failure_summary(&result, "Electron binary install failed.");
    log_install(
        install_dir,
        &format!("bun ./node_modules/electron/install.js failed\n{summary}"),
    )
    .await;

    let electron_dist_dir = electron_dist_dir_of(install_dir);
    if path_exists(&electron_dist_dir).await {
        log_install(
            install_dir,
            &format!(
                "Removing incomplete Electron binary folder before retry: {}",
                electron_dist_dir.display()
            ),
        )
        .await;
        if let Err(err) = fs::remove_dir_all(&electron_dist_dir).await {
            log_install(
                install_dir,
                &format!("Failed to remove incomplete Electron binary folder: {err}"),
            )
            .await;
            return Err(
                "Stella could not repair the desktop app. Try installing again.".to_string(),
            );
        }
    }

    set_step_progress(
        state,
        app,
        &SetupStepId::Payload,
        "Preparing Electron",
        Some(0.97),
    );
    let retry = run(
        &["bun", "./node_modules/electron/install.js"],
        Some(Path::new(install_dir)),
    )
    .await;
    if retry.ok {
        log_install(install_dir, "Electron binary prepared after repair").await;
        return Ok(());
    }

    let retry_summary = run_failure_summary(&retry, "Electron binary install failed.");
    log_install(
        install_dir,
        &format!("bun ./node_modules/electron/install.js retry failed\n{retry_summary}"),
    )
    .await;
    Err("Stella could not prepare the desktop app. Try installing again.".to_string())
}

fn run_failure_summary(result: &crate::shell::RunResult, fallback: &str) -> String {
    if !result.stderr.is_empty() {
        result.stderr.clone()
    } else if !result.stdout.is_empty() {
        result.stdout.clone()
    } else {
        fallback.into()
    }
}

async fn run_bun_install_with_progress(
    install_dir: &str,
    cwd: Option<&Path>,
    state: &mut InstallerState,
    app: &AppHandle,
) -> crate::shell::RunResult {
    let mut command = Command::new("bun");
    command
        .args(["install", "--frozen-lockfile"])
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .env("PATH", std::env::var("PATH").unwrap_or_default())
        .env("STELLA_SKIP_BROWSER_HYDRATE", "1");
    if let Some(dir) = cwd {
        command.current_dir(dir);
    }
    #[cfg(target_os = "windows")]
    {
        command.creation_flags(0x08000000);
    }

    set_step_progress(
        state,
        app,
        &SetupStepId::Payload,
        "Installing dependencies with Bun",
        Some(0.82),
    );
    log_install(install_dir, "Installing desktop dependencies with Bun").await;

    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(_) => {
            return crate::shell::RunResult {
                ok: false,
                stdout: String::new(),
                stderr: "spawn failed".into(),
            };
        }
    };

    let stdout = child.stdout.take();
    let stderr = child.stderr.take();
    let (line_tx, mut line_rx) = tokio::sync::mpsc::unbounded_channel::<String>();
    let stdout_line_tx = line_tx.clone();
    let stdout_task = tokio::spawn(async move {
        let mut collected = String::new();
        if let Some(stdout) = stdout {
            let mut lines = BufReader::new(stdout).lines();
            while let Ok(Some(line)) = lines.next_line().await {
                let _ = stdout_line_tx.send(line.clone());
                collected.push_str(&line);
                collected.push('\n');
            }
        }
        collected.trim().to_string()
    });
    let stderr_task = tokio::spawn(async move {
        let mut collected = String::new();
        if let Some(stderr) = stderr {
            let mut lines = BufReader::new(stderr).lines();
            while let Ok(Some(line)) = lines.next_line().await {
                let _ = line_tx.send(line.clone());
                collected.push_str(&line);
                collected.push('\n');
            }
        }
        collected.trim().to_string()
    });

    let mut tick_count: u64 = 0;
    let mut latest_line = String::new();
    let status = loop {
        while let Ok(line) = line_rx.try_recv() {
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                latest_line = trimmed.chars().take(120).collect();
            }
        }
        match child.try_wait() {
            Ok(Some(status)) => break Ok(status),
            Ok(None) => {
                tick_count += 1;
                let elapsed = tick_count * 2;
                let progress = 0.82 + (0.12 * (1.0 - (-(elapsed as f64) / 45.0).exp()));
                let detail = if latest_line.is_empty() {
                    format!("Installing dependencies with Bun ({elapsed}s)")
                } else {
                    format!("Bun: {latest_line}")
                };
                set_step_progress(state, app, &SetupStepId::Payload, detail, Some(progress));
                tokio::time::sleep(std::time::Duration::from_secs(2)).await;
            }
            Err(err) => break Err(err),
        }
    };

    let stdout = stdout_task.await.unwrap_or_default();
    let stderr = stderr_task.await.unwrap_or_default();
    match status {
        Ok(status) => crate::shell::RunResult {
            ok: status.success(),
            stdout,
            stderr,
        },
        Err(_) => crate::shell::RunResult {
            ok: false,
            stdout,
            stderr: if stderr.is_empty() {
                "spawn failed".into()
            } else {
                stderr
            },
        },
    }
}

async fn ensure_mac_screen_capture_permissions_built(install_dir: &str) -> Result<(), String> {
    if !cfg!(target_os = "macos") {
        return Ok(());
    }

    let module_dir = mac_screen_capture_permissions_dir_of(install_dir);
    if !path_exists(&module_dir).await {
        return Ok(());
    }

    let native_binary = mac_screen_capture_permissions_binary_of(install_dir);
    if path_exists(&native_binary).await {
        return Ok(());
    }

    let result = run(&["bun", "run", "native_build"], Some(module_dir.as_path())).await;
    if !result.ok {
        if result.stderr.is_empty() {
            return Err("mac-screen-capture-permissions native build failed.".into());
        }
        return Err(format!(
            "mac-screen-capture-permissions native build failed: {}",
            result.stderr
        ));
    }

    if path_exists(&native_binary).await {
        Ok(())
    } else {
        Err("mac-screen-capture-permissions native binary is still missing after build.".into())
    }
}

async fn ensure_parakeet_model_downloaded(install_dir: &str) -> Result<(), String> {
    if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        return ensure_parakeet_coreml_model_downloaded(install_dir).await;
    }
    if parakeet_cpp_supported() {
        return ensure_parakeet_cpp_model_downloaded(install_dir).await;
    }
    Ok(())
}

// Apple Silicon: the Swift/CoreML helper downloads its own model (FluidAudio)
// into resources/parakeet via `--download`.
async fn ensure_parakeet_coreml_model_downloaded(install_dir: &str) -> Result<(), String> {
    let helper = parakeet_helper_of(install_dir);
    if !path_exists(&helper).await {
        log_install(
            install_dir,
            "Skipping Parakeet model download because the local dictation helper is not present.",
        )
        .await;
        return Ok(());
    }
    let cache = parakeet_cache_dir_of(install_dir);
    fs::create_dir_all(&cache)
        .await
        .map_err(|e| format!("Failed to prepare Parakeet model cache: {e}"))?;
    log_install(install_dir, "Downloading local Parakeet dictation model").await;
    let helper_str = helper.to_string_lossy().to_string();
    let cache_str = cache.to_string_lossy().to_string();
    let result = run(
        &[&helper_str, "--download", "--cache-root", &cache_str],
        Some(desktop_dir_of(install_dir).as_path()),
    )
    .await;
    if result.ok {
        Ok(())
    } else {
        let detail = if result.stderr.is_empty() {
            result.stdout
        } else {
            result.stderr
        };
        Err(format!("Parakeet model download failed: {detail}"))
    }
}

// Windows + Intel macOS: parakeet.cpp reads a GGUF we fetch directly into
// resources/parakeet-cpp (the helper itself never touches the network).
async fn ensure_parakeet_cpp_model_downloaded(install_dir: &str) -> Result<(), String> {
    let helper = parakeet_cpp_helper_of(install_dir);
    if !path_exists(&helper).await {
        log_install(
            install_dir,
            "Skipping Parakeet model download because the local dictation helper is not present.",
        )
        .await;
        return Ok(());
    }
    let target = parakeet_cpp_model_path_of(install_dir);
    if parakeet_cpp_model_present(&target).await {
        return Ok(());
    }
    let dir = parakeet_cpp_model_dir_of(install_dir);
    fs::create_dir_all(&dir)
        .await
        .map_err(|e| format!("Failed to prepare Parakeet model cache: {e}"))?;
    log_install(install_dir, "Downloading local Parakeet dictation model").await;

    let tmp = dir.join(format!("{PARAKEET_CPP_MODEL_FILE}.part"));
    let _ = fs::remove_file(&tmp).await;
    let client = download_client()?;
    let mut response = client
        .get(PARAKEET_CPP_MODEL_URL)
        .header("User-Agent", "stella-launcher")
        .send()
        .await
        .map_err(|e| format!("Parakeet model download failed: {e}"))?;
    if !response.status().is_success() {
        return Err(format!(
            "Parakeet model download failed ({}).",
            response.status()
        ));
    }
    {
        let mut file = fs::File::create(&tmp)
            .await
            .map_err(|e| format!("Failed to create Parakeet model download: {e}"))?;
        while let Some(chunk) = response
            .chunk()
            .await
            .map_err(|e| format!("Failed to read Parakeet model download: {e}"))?
        {
            file.write_all(&chunk)
                .await
                .map_err(|e| format!("Failed to write Parakeet model download: {e}"))?;
        }
        file.flush()
            .await
            .map_err(|e| format!("Failed to finish Parakeet model download: {e}"))?;
    }

    let digest = sha256_file_digest(&tmp).await?;
    if let Err(err) = verify_sha256_digest(digest, PARAKEET_CPP_MODEL_SHA256) {
        let _ = fs::remove_file(&tmp).await;
        return Err(err);
    }
    fs::rename(&tmp, &target)
        .await
        .map_err(|e| format!("Failed to finalize Parakeet model: {e}"))?;
    Ok(())
}

async fn ripgrep_private_binary_exists() -> bool {
    path_exists(&ripgrep_private_binary_path()).await
}

async fn download_ripgrep_archive(target: &Path, url: &str) -> Result<(), String> {
    let client = download_client()?;
    let mut response = client
        .get(url)
        .header("User-Agent", "stella-launcher")
        .send()
        .await
        .map_err(|e| format!("Ripgrep download failed: {e}"))?;
    if !response.status().is_success() {
        return Err(format!("Ripgrep download failed ({}).", response.status()));
    }

    let mut file = fs::File::create(target)
        .await
        .map_err(|e| format!("Failed to create ripgrep download: {e}"))?;
    while let Some(chunk) = response
        .chunk()
        .await
        .map_err(|e| format!("Failed to read ripgrep download: {e}"))?
    {
        file.write_all(&chunk)
            .await
            .map_err(|e| format!("Failed to write ripgrep download: {e}"))?;
    }
    file.flush()
        .await
        .map_err(|e| format!("Failed to finish ripgrep download: {e}"))?;
    Ok(())
}

fn powershell_single_quoted(value: &str) -> String {
    format!("'{}'", value.replace('\'', "''"))
}

async fn extract_ripgrep_archive(
    archive_path: &Path,
    extract_dir: &Path,
    extension: &str,
) -> Result<(), String> {
    if extension == "zip" {
        let archive = archive_path.to_string_lossy().to_string();
        let destination = extract_dir.to_string_lossy().to_string();
        let script = format!(
            "$global:ProgressPreference = 'SilentlyContinue'; Expand-Archive -LiteralPath {} -DestinationPath {} -Force",
            powershell_single_quoted(&archive),
            powershell_single_quoted(&destination),
        );
        let result = run(
            &[
                "powershell.exe",
                "-NoProfile",
                "-NonInteractive",
                "-Command",
                &script,
            ],
            None,
        )
        .await;
        if result.ok {
            return Ok(());
        }
        let fallback = run(
            &[
                "pwsh.exe",
                "-NoProfile",
                "-NonInteractive",
                "-Command",
                &script,
            ],
            None,
        )
        .await;
        if fallback.ok {
            return Ok(());
        }
        return Err(run_failure_summary(
            &fallback,
            "Could not extract ripgrep archive.",
        ));
    }

    let archive = archive_path.to_string_lossy().to_string();
    let destination = extract_dir.to_string_lossy().to_string();
    let result = run(&["tar", "-xzf", &archive, "-C", &destination], None).await;
    if result.ok {
        Ok(())
    } else {
        Err(run_failure_summary(
            &result,
            "Could not extract ripgrep archive.",
        ))
    }
}

async fn ensure_ripgrep_provisioned(install_dir: &str) -> Result<(), String> {
    let target = ripgrep_private_binary_path();
    if path_exists(&target).await {
        log_install(
            install_dir,
            "Ripgrep already available in Stella private bin",
        )
        .await;
        return Ok(());
    }

    let Some((platform, extension)) = ripgrep_platform_asset() else {
        log_install(
            install_dir,
            "Skipping ripgrep provisioning on unsupported platform",
        )
        .await;
        return Ok(());
    };

    let bin_dir = stella_private_bin_dir();
    fs::create_dir_all(&bin_dir)
        .await
        .map_err(|e| format!("Failed to create Stella private bin: {e}"))?;

    let filename = format!("ripgrep-{RIPGREP_VERSION}-{platform}.{extension}");
    let url = format!(
        "https://github.com/BurntSushi/ripgrep/releases/download/{RIPGREP_VERSION}/{filename}"
    );
    let archive_path = bin_dir.join(&filename);
    let extract_dir = bin_dir.join(format!("ripgrep-{RIPGREP_VERSION}-extract"));

    log_install(install_dir, &format!("Downloading ripgrep from {url}")).await;
    let result = async {
        let _ = fs::remove_dir_all(&extract_dir).await;
        fs::create_dir_all(&extract_dir)
            .await
            .map_err(|e| format!("Failed to prepare ripgrep extract dir: {e}"))?;
        download_ripgrep_archive(&archive_path, &url).await?;
        extract_ripgrep_archive(&archive_path, &extract_dir, extension).await?;

        let extracted = extract_dir
            .join(format!("ripgrep-{RIPGREP_VERSION}-{platform}"))
            .join(ripgrep_executable_name());
        if !path_exists(&extracted).await {
            return Err("Ripgrep archive did not contain the expected executable.".to_string());
        }
        fs::copy(&extracted, &target)
            .await
            .map_err(|e| format!("Failed to install ripgrep: {e}"))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = fs::metadata(&target)
                .await
                .map_err(|e| format!("Failed to inspect ripgrep permissions: {e}"))?
                .permissions();
            perms.set_mode(0o755);
            fs::set_permissions(&target, perms)
                .await
                .map_err(|e| format!("Failed to mark ripgrep executable: {e}"))?;
        }
        Ok(())
    }
    .await;

    let _ = fs::remove_file(&archive_path).await;
    let _ = fs::remove_dir_all(&extract_dir).await;

    result?;
    log_install(
        install_dir,
        &format!("Ripgrep installed to {}", target.to_string_lossy()),
    )
    .await;
    Ok(())
}

// ── Clone-based desktop install ─────────────────────────────────────

async fn remove_path_if_present(path: &Path) -> Result<(), String> {
    let Ok(metadata) = fs::symlink_metadata(path).await else {
        return Ok(());
    };
    if metadata.is_dir() && !metadata.file_type().is_symlink() {
        fs::remove_dir_all(path)
            .await
            .map_err(|e| format!("Failed to remove {}: {e}", path.to_string_lossy()))
    } else {
        fs::remove_file(path)
            .await
            .map_err(|e| format!("Failed to remove {}: {e}", path.to_string_lossy()))
    }
}

async fn install_managed_node(
    client: &reqwest::Client,
    install_dir: &str,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<PathBuf, String> {
    let asset = managed_node_asset().ok_or_else(|| {
        format!(
            "Stella's managed Node runtime is not available for {}/{}.",
            std::env::consts::OS,
            std::env::consts::ARCH
        )
    })?;
    let archive_path = managed_node_archive_path()?;
    fs::create_dir_all(managed_node_cache_dir())
        .await
        .map_err(|e| format!("Failed to prepare Stella's Node cache: {e}"))?;
    set_step_progress(
        state,
        app,
        &SetupStepId::Runtime,
        "Installing Stella's managed Node runtime",
        Some(0.35),
    );
    download_archive_with_resume(
        client,
        asset.url,
        &archive_path,
        None,
        Some(asset.sha256),
        install_dir,
        state,
        app,
        SetupStepId::Runtime,
        "Node",
        0.35,
        0.2,
    )
    .await?;

    let target = managed_node_dir();
    let staging = target
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join(format!(".{MANAGED_NODE_VERSION}-extracting"));
    remove_path_if_present(&staging).await?;
    remove_path_if_present(&target).await?;
    fs::create_dir_all(&staging)
        .await
        .map_err(|e| format!("Failed to prepare Node extraction: {e}"))?;

    if cfg!(target_os = "windows") {
        let archive = archive_path.to_string_lossy().to_string();
        let destination = staging.to_string_lossy().to_string();
        let mut command = Command::new("powershell");
        command.args([
            "-NoProfile",
            "-NonInteractive",
            "-ExecutionPolicy",
            "Bypass",
            "-Command",
            &format!(
                "Expand-Archive -LiteralPath '{}' -DestinationPath '{}' -Force",
                archive.replace('\'', "''"),
                destination.replace('\'', "''")
            ),
        ]);
        #[cfg(target_os = "windows")]
        {
            command.creation_flags(0x08000000);
        }
        let output = command
            .output()
            .await
            .map_err(|e| format!("Failed to extract Node: {e}"))?;
        if !output.status.success() {
            return Err(format!(
                "Failed to extract Node: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        let mut entries = fs::read_dir(&staging)
            .await
            .map_err(|e| format!("Failed to inspect Node archive: {e}"))?;
        let extracted_root = entries
            .next_entry()
            .await
            .map_err(|e| format!("Failed to inspect Node archive: {e}"))?
            .map(|entry| entry.path())
            .ok_or_else(|| "Node archive was empty.".to_string())?;
        fs::rename(&extracted_root, &target)
            .await
            .map_err(|e| format!("Failed to install Node: {e}"))?;
        remove_path_if_present(&staging).await?;
    } else {
        let archive_for_extract = archive_path.clone();
        let staging_for_extract = staging.clone();
        tokio::task::spawn_blocking(move || {
            let file = std::fs::File::open(&archive_for_extract)
                .map_err(|e| format!("Failed to open Node archive: {e}"))?;
            let decoder = GzDecoder::new(file);
            let mut archive = tar::Archive::new(decoder);
            for entry in archive
                .entries()
                .map_err(|e| format!("Failed to read Node archive: {e}"))?
            {
                let mut entry = entry.map_err(|e| format!("Failed to read Node entry: {e}"))?;
                let path = entry
                    .path()
                    .map_err(|e| format!("Failed to read Node entry path: {e}"))?;
                let relative = path.components().skip(1).collect::<PathBuf>();
                if relative.as_os_str().is_empty()
                    || relative.components().any(|component| {
                        !matches!(
                            component,
                            std::path::Component::Normal(_) | std::path::Component::CurDir
                        )
                    })
                {
                    continue;
                }
                entry
                    .unpack(staging_for_extract.join(relative))
                    .map_err(|e| format!("Failed to extract Node entry: {e}"))?;
            }
            Ok::<(), String>(())
        })
        .await
        .map_err(|e| format!("Node extraction task failed: {e}"))??;
        fs::rename(&staging, &target)
            .await
            .map_err(|e| format!("Failed to install Node: {e}"))?;
    }

    let binary = managed_node_binary();
    if !managed_node_is_usable() {
        return Err("Stella's managed Node runtime was incomplete.".into());
    }
    log_install(
        install_dir,
        &format!(
            "Node {MANAGED_NODE_VERSION} installed to {}",
            target.to_string_lossy()
        ),
    )
    .await;
    Ok(binary)
}

async fn ensure_node_runtime(
    client: &reqwest::Client,
    install_dir: &str,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<PathBuf, String> {
    if let Some(system) = system_node_binary() {
        log_install(
            install_dir,
            &format!("Using existing Node at {}", system.to_string_lossy()),
        )
        .await;
        return Ok(system);
    }
    if managed_node_is_usable() {
        return Ok(managed_node_binary());
    }
    install_managed_node(client, install_dir, state, app).await
}

async fn ensure_uv_runtime(client: &reqwest::Client, install_dir: &str) -> Result<PathBuf, String> {
    if let Some(system) = usable_executable_on_path(
        if cfg!(target_os = "windows") {
            "uv.exe"
        } else {
            "uv"
        },
        &["--version"],
    ) {
        return Ok(system);
    }
    let managed = managed_uv_binary();
    if command_succeeds(&managed, &["--version"]) {
        return Ok(managed);
    }

    fs::create_dir_all(stella_private_bin_dir())
        .await
        .map_err(|e| format!("Failed to prepare Stella's private bin directory: {e}"))?;
    let installer_url = if cfg!(target_os = "windows") {
        format!("https://astral.sh/uv/{MANAGED_UV_VERSION}/install.ps1")
    } else {
        format!("https://astral.sh/uv/{MANAGED_UV_VERSION}/install.sh")
    };
    let installer = fetch_required_text(client, &installer_url).await?;
    let installer_path =
        stella_data_dir()
            .join("cache")
            .join("launcher")
            .join(if cfg!(target_os = "windows") {
                "install-uv.ps1"
            } else {
                "install-uv.sh"
            });
    if let Some(parent) = installer_path.parent() {
        fs::create_dir_all(parent)
            .await
            .map_err(|e| format!("Failed to prepare uv installer cache: {e}"))?;
    }
    fs::write(&installer_path, installer)
        .await
        .map_err(|e| format!("Failed to cache uv installer: {e}"))?;

    let mut command = if cfg!(target_os = "windows") {
        let mut command = Command::new("powershell");
        command.args([
            "-NoProfile",
            "-NonInteractive",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            installer_path.to_string_lossy().as_ref(),
        ]);
        #[cfg(target_os = "windows")]
        {
            command.creation_flags(0x08000000);
        }
        command
    } else {
        let mut command = Command::new("sh");
        command.arg(&installer_path);
        command
    };
    command
        .env("UV_UNMANAGED_INSTALL", stella_private_bin_dir())
        .env("UV_NO_MODIFY_PATH", "1");
    let output = command
        .output()
        .await
        .map_err(|e| format!("Failed to install uv: {e}"))?;
    if !output.status.success() || !command_succeeds(&managed, &["--version"]) {
        let detail = String::from_utf8_lossy(&output.stderr).trim().to_string();
        return Err(if detail.is_empty() {
            "uv installation did not produce a usable binary.".into()
        } else {
            format!("Failed to install uv: {detail}")
        });
    }
    log_install(
        install_dir,
        &format!("uv installed to {}", managed.to_string_lossy()),
    )
    .await;
    Ok(managed)
}

async fn ensure_python_command_shims(python: &Path) -> Result<(), String> {
    if python.parent() == Some(stella_private_bin_dir().as_path()) {
        return Ok(());
    }
    fs::create_dir_all(stella_private_bin_dir())
        .await
        .map_err(|e| format!("Failed to prepare Stella's private bin directory: {e}"))?;
    if cfg!(target_os = "windows") {
        for name in ["python.cmd", "python3.cmd"] {
            let content = format!("@echo off\r\n\"{}\" %*\r\n", python.to_string_lossy());
            fs::write(stella_private_bin_dir().join(name), content)
                .await
                .map_err(|e| format!("Failed to create {name}: {e}"))?;
        }
    } else {
        for name in ["python", "python3"] {
            let path = stella_private_bin_dir().join(name);
            let content = format!("#!/bin/sh\nexec \"{}\" \"$@\"\n", python.to_string_lossy());
            fs::write(&path, content)
                .await
                .map_err(|e| format!("Failed to create {name}: {e}"))?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let mut permissions = fs::metadata(&path)
                    .await
                    .map_err(|e| format!("Failed to inspect {name}: {e}"))?
                    .permissions();
                permissions.set_mode(0o755);
                fs::set_permissions(&path, permissions)
                    .await
                    .map_err(|e| format!("Failed to make {name} executable: {e}"))?;
            }
        }
    }
    Ok(())
}

async fn ensure_python_runtime(
    client: &reqwest::Client,
    install_dir: &str,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<PathBuf, String> {
    if let Some(system) = python_command_names()
        .iter()
        .find_map(|name| executable_on_path(name).filter(|path| python_version_is_usable(path)))
    {
        ensure_python_command_shims(&system).await?;
        log_install(
            install_dir,
            &format!("Using existing Python at {}", system.to_string_lossy()),
        )
        .await;
        return Ok(system);
    }
    if let Some(managed) = python_command_names().iter().find_map(|name| {
        let candidate = stella_private_bin_dir().join(name);
        python_version_is_usable(&candidate).then_some(candidate)
    }) {
        ensure_python_command_shims(&managed).await?;
        return Ok(managed);
    }

    set_step_progress(
        state,
        app,
        &SetupStepId::Runtime,
        "Installing Stella's managed Python runtime",
        Some(0.6),
    );
    let uv = ensure_uv_runtime(client, install_dir).await?;
    fs::create_dir_all(managed_python_install_dir())
        .await
        .map_err(|e| format!("Failed to prepare Stella's Python runtime: {e}"))?;
    fs::create_dir_all(stella_private_bin_dir())
        .await
        .map_err(|e| format!("Failed to prepare Stella's private bin directory: {e}"))?;
    let mut command = Command::new(&uv);
    command
        .args(["python", "install", MANAGED_PYTHON_VERSION, "--default"])
        .env("UV_PYTHON_INSTALL_DIR", managed_python_install_dir())
        .env("UV_PYTHON_BIN_DIR", stella_private_bin_dir())
        .env("UV_CACHE_DIR", stella_data_dir().join("cache").join("uv"));
    #[cfg(target_os = "windows")]
    {
        command.creation_flags(0x08000000);
    }
    let output = command
        .output()
        .await
        .map_err(|e| format!("Failed to install Python: {e}"))?;
    if !output.status.success() {
        let detail = String::from_utf8_lossy(&output.stderr).trim().to_string();
        return Err(if detail.is_empty() {
            "Python installation failed.".into()
        } else {
            format!("Python installation failed: {detail}")
        });
    }
    let python = python_command_names()
        .iter()
        .find_map(|name| {
            let candidate = stella_private_bin_dir().join(name);
            python_version_is_usable(&candidate).then_some(candidate)
        })
        .ok_or_else(|| "Python installation did not produce python/python3 shims.".to_string())?;
    ensure_python_command_shims(&python).await?;
    log_install(
        install_dir,
        &format!(
            "Python installed to {}",
            managed_python_install_dir().to_string_lossy()
        ),
    )
    .await;
    Ok(python)
}

async fn prepare_git_runtime(
    client: &reqwest::Client,
    install_dir: &str,
    state: &mut InstallerState,
    app: &AppHandle,
    step_id: SetupStepId,
) -> Result<GitRuntime, String> {
    if let Some(system) = system_git_runtime() {
        log_install(
            install_dir,
            &format!("Using existing Git at {}", system.bin.to_string_lossy()),
        )
        .await;
        return Ok(system);
    }

    if let Some(managed) = managed_git_runtime() {
        log_install(
            install_dir,
            &format!(
                "Using Stella's managed Git at {}",
                managed.bin.to_string_lossy()
            ),
        )
        .await;
        return Ok(managed);
    }

    let manifest_url = git_runtime_manifest_url();
    log_install(
        install_dir,
        &format!("Resolving Git runtime manifest: {manifest_url}"),
    )
    .await;
    let manifest_text = fetch_required_text(client, &manifest_url).await?;
    let manifest = serde_json::from_str::<ManagedGitManifest>(&manifest_text)
        .map_err(|e| format!("Git runtime manifest was invalid JSON: {e}"))?;
    let asset = resolve_managed_git_asset(manifest)?;
    let cache_dir = managed_git_dir();
    let archive_path = managed_git_archive_path(&asset);
    let git_root = managed_git_root();
    let git_bin = git_bin_of_root(&git_root);

    if path_exists(&git_bin).await && managed_git_runtime().is_some() {
        return managed_git_runtime()
            .ok_or_else(|| "Stella's managed Git runtime was invalid.".to_string());
    }

    fs::create_dir_all(&cache_dir)
        .await
        .map_err(|e| format!("Failed to prepare Stella's Git cache: {e}"))?;
    set_step_progress(
        state,
        app,
        &step_id,
        "Preparing Stella's managed Git",
        Some(0.04),
    );
    download_archive_with_resume(
        client,
        &asset.url,
        &archive_path,
        Some(asset.size),
        Some(&asset.sha256),
        install_dir,
        state,
        app,
        step_id,
        "Git",
        0.04,
        0.12,
    )
    .await?;

    remove_path_if_present(&git_root).await?;
    fs::create_dir_all(&git_root)
        .await
        .map_err(|e| format!("Failed to prepare Stella's managed Git runtime: {e}"))?;
    let archive_for_extract = archive_path.clone();
    let root_for_extract = git_root.clone();
    tokio::task::spawn_blocking(move || {
        let file = std::fs::File::open(&archive_for_extract)
            .map_err(|e| format!("Failed to open Stella's Git runtime: {e}"))?;
        let decoder = GzDecoder::new(file);
        let mut archive = tar::Archive::new(decoder);
        for entry in archive
            .entries()
            .map_err(|e| format!("Failed to read Stella's Git runtime: {e}"))?
        {
            let mut entry =
                entry.map_err(|e| format!("Failed to read a Git runtime entry: {e}"))?;
            entry
                .unpack_in(&root_for_extract)
                .map_err(|e| format!("Failed to extract Stella's Git runtime: {e}"))?;
        }
        Ok::<(), String>(())
    })
    .await
    .map_err(|e| format!("Git extraction task failed: {e}"))??;

    if !path_exists(&git_bin).await {
        return Err("Stella's managed Git runtime was incomplete.".into());
    }
    log_install(
        install_dir,
        &format!(
            "Prepared checksum-verified managed Git runtime at {}",
            git_root.to_string_lossy()
        ),
    )
    .await;
    managed_git_runtime().ok_or_else(|| "Stella's managed Git runtime was invalid.".to_string())
}

async fn run_git_runtime(
    git: &GitRuntime,
    cwd: Option<&Path>,
    args: &[String],
) -> Result<std::process::Output, String> {
    let mut command = Command::new(&git.bin);
    command
        .args(args)
        .envs(&git.env)
        .env("GIT_TERMINAL_PROMPT", "0")
        .env("GIT_LFS_SKIP_SMUDGE", "1");
    if let Some(cwd) = cwd {
        command.current_dir(cwd);
    }
    #[cfg(target_os = "windows")]
    {
        command.creation_flags(0x08000000);
    }
    command
        .output()
        .await
        .map_err(|e| format!("Could not run Git: {e}"))
}

fn git_output_error(action: &str, output: &std::process::Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
    let detail = if !stderr.is_empty() { stderr } else { stdout };
    if detail.is_empty() {
        format!("{action} failed.")
    } else {
        format!("{action} failed: {detail}")
    }
}

async fn git_stdout(git: &GitRuntime, cwd: &Path, args: &[&str]) -> Result<String, String> {
    let owned = args
        .iter()
        .map(|arg| (*arg).to_string())
        .collect::<Vec<_>>();
    let output = run_git_runtime(git, Some(cwd), &owned).await?;
    if !output.status.success() {
        return Err(git_output_error("Git inspection", &output));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

async fn move_clone_into_install(clone_dir: &Path, install_dir: &Path) -> Result<(), String> {
    let mut entries = fs::read_dir(clone_dir)
        .await
        .map_err(|e| format!("Failed to read cloned Stella source: {e}"))?;
    while let Some(entry) = entries
        .next_entry()
        .await
        .map_err(|e| format!("Failed to read cloned Stella source: {e}"))?
    {
        let target = install_dir.join(entry.file_name());
        remove_path_if_present(&target).await?;
        fs::rename(entry.path(), &target)
            .await
            .map_err(|e| format!("Failed to install cloned Stella source: {e}"))?;
    }
    fs::remove_dir(clone_dir)
        .await
        .map_err(|e| format!("Failed to finish cloned Stella source: {e}"))
}

async fn clone_release_source(
    release: &ResolvedDesktopRelease,
    git: &GitRuntime,
    install_dir: &str,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<(), String> {
    let install_path = Path::new(install_dir);
    let existing_git = install_path.join(".git");
    if path_exists(&existing_git).await {
        let existing_head = git_stdout(git, install_path, &["rev-parse", "HEAD"]).await?;
        if existing_head == release.commit {
            log_install(
                install_dir,
                &format!("Existing clone already matches {}", release.commit),
            )
            .await;
            return Ok(());
        }
        return Err(
            "The selected Stella folder has different Git history. Choose a new folder or update the existing installation."
                .into(),
        );
    }

    let clone_dir = source_clone_dir_of(install_dir);
    remove_path_if_present(&clone_dir).await?;
    set_step_progress(
        state,
        app,
        &SetupStepId::Payload,
        "Cloning Stella",
        Some(0.18),
    );
    let clone_args = vec![
        "clone".into(),
        "--filter=blob:none".into(),
        "--no-checkout".into(),
        "--no-tags".into(),
        STELLA_GITHUB_REMOTE_URL.into(),
        clone_dir.to_string_lossy().to_string(),
    ];
    let clone_output = run_git_runtime(git, None, &clone_args).await?;
    if !clone_output.status.success() {
        return Err(git_output_error("Cloning Stella", &clone_output));
    }

    set_step_progress(
        state,
        app,
        &SetupStepId::Payload,
        "Checking out this Stella release",
        Some(0.38),
    );
    let checkout_args = vec![
        "checkout".into(),
        "--force".into(),
        "-B".into(),
        "master".into(),
        release.commit.clone(),
    ];
    let checkout_output = run_git_runtime(git, Some(&clone_dir), &checkout_args).await?;
    if !checkout_output.status.success() {
        return Err(git_output_error(
            "Checking out the Stella release",
            &checkout_output,
        ));
    }

    let remote_head = git_stdout(git, &clone_dir, &["rev-parse", "origin/master"]).await?;
    if remote_head != release.commit {
        return Err(format!(
            "Published Stella commit {} did not match origin/master {}.",
            release.commit, remote_head
        ));
    }
    let upstream_args = vec![
        "branch".into(),
        "--set-upstream-to=origin/master".into(),
        "master".into(),
    ];
    let upstream_output = run_git_runtime(git, Some(&clone_dir), &upstream_args).await?;
    if !upstream_output.status.success() {
        return Err(git_output_error(
            "Configuring Stella's update branch",
            &upstream_output,
        ));
    }

    move_clone_into_install(&clone_dir, install_path).await?;
    let installed_head = git_stdout(git, install_path, &["rev-parse", "HEAD"]).await?;
    if installed_head != release.commit {
        return Err("Installed Stella clone did not retain the published commit.".into());
    }
    let partial_filter = git_stdout(
        git,
        install_path,
        &["config", "--get", "remote.origin.partialclonefilter"],
    )
    .await?;
    if partial_filter != "blob:none" {
        return Err("Installed Stella clone did not retain blobless history.".into());
    }
    let status = git_stdout(
        git,
        install_path,
        &["status", "--porcelain", "--untracked-files=all"],
    )
    .await?;
    if !status.is_empty() {
        return Err(
            "The selected Stella folder contained files that do not match the published release. Choose a new folder."
                .into(),
        );
    }
    log_install(
        install_dir,
        &format!(
            "Cloned Stella at exact upstream commit {} with blobless history",
            release.commit
        ),
    )
    .await;
    Ok(())
}

async fn write_cloned_release_manifest(
    install_dir: &str,
    release: &ResolvedDesktopRelease,
) -> Result<(), String> {
    let version = release
        .tag
        .strip_prefix("desktop-v")
        .unwrap_or(&release.tag);
    let manifest = serde_json::json!({
        "schemaVersion": 1,
        "tag": release.tag,
        "version": version,
        "platform": release.platform,
        "commit": release.commit,
        "files": {},
    });
    let bytes = serde_json::to_vec_pretty(&manifest)
        .map_err(|e| format!("Failed to serialize Stella release metadata: {e}"))?;
    fs::write(release_manifest_of(install_dir), bytes)
        .await
        .map_err(|e| format!("Failed to write Stella release metadata: {e}"))
}

async fn download_and_clone_release(
    install_dir: &str,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<ResolvedDesktopRelease, String> {
    let client = download_client()?;
    fs::create_dir_all(install_dir)
        .await
        .map_err(|e| format!("Failed to prepare Stella's install folder: {e}"))?;
    set_step_progress(
        state,
        app,
        &SetupStepId::Payload,
        "Resolving Stella release",
        Some(0.02),
    );
    let release = resolve_r2_desktop_release(&client, install_dir).await?;
    let git = prepare_git_runtime(&client, install_dir, state, app, SetupStepId::Payload).await?;
    clone_release_source(&release, &git, install_dir, state, app).await?;
    write_cloned_release_manifest(install_dir, &release).await?;

    log_install(
        install_dir,
        &format!(
            "Stella source ready at {} ({})",
            release.tag, release.commit
        ),
    )
    .await;
    set_step_progress(
        state,
        app,
        &SetupStepId::Payload,
        "Stella source is ready",
        Some(0.45),
    );
    Ok(release)
}

fn pinned_artifact<'a>(
    release: &'a ResolvedDesktopRelease,
    kind: &str,
) -> Result<&'a DesktopArtifactRef, String> {
    release
        .artifact_refs
        .iter()
        .find(|reference| reference.kind == kind && reference.platform == release.platform)
        .ok_or_else(|| {
            format!(
                "Desktop release {} did not pin {kind} for {}.",
                release.tag, release.platform
            )
        })
}

fn validate_pinned_artifact(reference: &DesktopArtifactRef) -> Result<String, String> {
    if !reference.asset.url.starts_with("https://") || reference.asset.size_bytes == 0 {
        return Err(format!(
            "Published {} artifact metadata was invalid.",
            reference.kind
        ));
    }
    normalize_sha256(&reference.asset.sha256).ok_or_else(|| {
        format!(
            "Published {} artifact checksum was invalid.",
            reference.kind
        )
    })
}

fn artifact_revision_from_url(url: &str, segment: &str) -> Option<String> {
    let parts = url.split('/').collect::<Vec<_>>();
    let index = parts.iter().position(|part| *part == segment)?;
    let revision = *parts.get(index + 1)?;
    valid_release_commit(revision).then(|| revision.to_ascii_lowercase())
}

async fn install_native_helpers_artifact(
    client: &reqwest::Client,
    install_dir: &str,
    release: &ResolvedDesktopRelease,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<(), String> {
    let reference = pinned_artifact(release, "native-helpers")?;
    let sha256 = validate_pinned_artifact(reference)?;
    let archive_path = Path::new(install_dir).join(".stella-native-helpers-download.tar.zst");
    download_archive_with_resume(
        client,
        &reference.asset.url,
        &archive_path,
        Some(reference.asset.size_bytes),
        Some(&sha256),
        install_dir,
        state,
        app,
        SetupStepId::Payload,
        "native components",
        0.48,
        0.1,
    )
    .await?;

    set_step_progress(
        state,
        app,
        &SetupStepId::Payload,
        "Installing native components",
        Some(0.59),
    );
    let target = native_helpers_dir_of(install_dir);
    remove_path_if_present(&target).await?;
    fs::create_dir_all(&target)
        .await
        .map_err(|e| format!("Failed to prepare native components: {e}"))?;
    let archive_for_extract = archive_path.clone();
    let target_for_extract = target.clone();
    tokio::task::spawn_blocking(move || {
        let file = std::fs::File::open(&archive_for_extract)
            .map_err(|e| format!("Failed to open native components: {e}"))?;
        let decoder = zstd::Decoder::new(file)
            .map_err(|e| format!("Failed to decompress native components: {e}"))?;
        let mut archive = tar::Archive::new(decoder);
        for entry in archive
            .entries()
            .map_err(|e| format!("Failed to read native components: {e}"))?
        {
            let mut entry = entry.map_err(|e| format!("Failed to read a native component: {e}"))?;
            entry
                .unpack_in(&target_for_extract)
                .map_err(|e| format!("Failed to install a native component: {e}"))?;
        }
        Ok::<(), String>(())
    })
    .await
    .map_err(|e| format!("Native component extraction task failed: {e}"))??;

    let marker = serde_json::json!({
        "schemaVersion": 1,
        "sourceManifestUrl": reference.manifest_url,
        "platform": reference.platform,
        "helperPlatformDir": native_helpers_platform_dir(),
        "sha": reference.manifest_sha,
        "commit": reference.commit,
        "builtAt": reference.built_at,
        "installedAt": chrono_now(),
        "installMode": "archive",
        "asset": {
            "url": reference.asset.url,
            "sha256": sha256,
            "size": reference.asset.size_bytes,
        },
    });
    fs::write(
        target.join(".stella-native-helpers.json"),
        serde_json::to_vec_pretty(&marker)
            .map_err(|e| format!("Failed to serialize native component metadata: {e}"))?,
    )
    .await
    .map_err(|e| format!("Failed to write native component metadata: {e}"))?;
    let _ = fs::remove_file(&archive_path).await;
    Ok(())
}

async fn install_browser_artifact(
    client: &reqwest::Client,
    install_dir: &str,
    release: &ResolvedDesktopRelease,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<(), String> {
    let reference = pinned_artifact(release, "stella-browser")?;
    let sha256 = validate_pinned_artifact(reference)?;
    let temp_path = Path::new(install_dir).join(".stella-browser-download");
    download_archive_with_resume(
        client,
        &reference.asset.url,
        &temp_path,
        Some(reference.asset.size_bytes),
        Some(&sha256),
        install_dir,
        state,
        app,
        SetupStepId::Payload,
        "browser service",
        0.6,
        0.08,
    )
    .await?;

    let target_dir = desktop_dir_of(install_dir)
        .join("stella-browser")
        .join("out")
        .join(&release.platform);
    fs::create_dir_all(&target_dir)
        .await
        .map_err(|e| format!("Failed to prepare browser service: {e}"))?;
    let binary_name = if cfg!(target_os = "windows") {
        "stella-browser.exe"
    } else {
        "stella-browser"
    };
    let binary_path = target_dir.join(binary_name);
    remove_path_if_present(&binary_path).await?;
    fs::rename(&temp_path, &binary_path)
        .await
        .map_err(|e| format!("Failed to install browser service: {e}"))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut permissions = fs::metadata(&binary_path)
            .await
            .map_err(|e| format!("Failed to inspect browser service: {e}"))?
            .permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&binary_path, permissions)
            .await
            .map_err(|e| format!("Failed to mark browser service executable: {e}"))?;
    }

    let source_sha = artifact_revision_from_url(&reference.asset.url, "stella-browser");
    let marker = serde_json::json!({
        "schemaVersion": 1,
        "sourceManifestUrl": serde_json::Value::Null,
        "sourceManifestFile": serde_json::Value::Null,
        "sourceSha": source_sha,
        "platform": reference.platform,
        "asset": {
            "url": reference.asset.url,
            "sha256": sha256,
            "size": reference.asset.size_bytes,
        },
        "installedAt": chrono_now(),
    });
    fs::write(
        target_dir.join(".stella-browser.json"),
        serde_json::to_vec_pretty(&marker)
            .map_err(|e| format!("Failed to serialize browser service metadata: {e}"))?,
    )
    .await
    .map_err(|e| format!("Failed to write browser service metadata: {e}"))?;
    Ok(())
}

async fn install_release_artifacts(
    install_dir: &str,
    release: &ResolvedDesktopRelease,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<(), String> {
    let client = download_client()?;
    install_native_helpers_artifact(&client, install_dir, release, state, app).await?;
    install_browser_artifact(&client, install_dir, release, state, app).await?;
    log_install(
        install_dir,
        "Installed release-pinned native components and browser service",
    )
    .await;
    Ok(())
}

async fn remove_install_files(install_path: &str) -> Result<(), String> {
    // Durable user data lives in `~/.stella` (set as STELLA_DATA_DIR on launch),
    // outside the install tree, so normal uninstall removes the install root.
    remove_dir_all_tolerating_windows_lock(
        Path::new(install_path),
        "Failed to remove Stella directory",
    )
    .await
}

fn is_transient_windows_remove_error(error: &io::Error) -> bool {
    if !cfg!(target_os = "windows") {
        return false;
    }

    // ERROR_SHARING_VIOLATION, ERROR_LOCK_VIOLATION, ERROR_DIR_NOT_EMPTY.
    // The last can surface after a recursive remove partially succeeds while
    // a child path is still being released by a recently-killed process.
    matches!(error.raw_os_error(), Some(32 | 33 | 145))
}

async fn remove_dir_all_tolerating_windows_lock(path: &Path, context: &str) -> Result<(), String> {
    let deadline = Instant::now() + WINDOWS_REMOVE_RETRY_TIMEOUT;
    loop {
        match fs::remove_dir_all(path).await {
            Ok(()) => return Ok(()),
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
            Err(error) => {
                if is_transient_windows_remove_error(&error) && Instant::now() < deadline {
                    sleep(WINDOWS_REMOVE_RETRY_POLL).await;
                    continue;
                }
                return Err(format!("{context}: {error}"));
            }
        }
    }
}

async fn fetch_required_text(client: &reqwest::Client, url: &str) -> Result<String, String> {
    let response = client
        .get(url)
        .header("User-Agent", "stella-launcher")
        .send()
        .await
        .map_err(|e| format!("Request failed for {url}: {e}"))?;
    if !response.status().is_success() {
        return Err(format!(
            "Request failed for {url}: HTTP {}",
            response.status()
        ));
    }
    response
        .text()
        .await
        .map_err(|e| format!("Failed to read response body from {url}: {e}"))
}

fn sha256_digest_hex(digest: Sha256) -> String {
    let hash = digest.finalize();
    hash.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn verify_sha256_digest(digest: Sha256, expected: &str) -> Result<(), String> {
    let normalized = normalize_sha256(expected)
        .ok_or_else(|| "Release checksum metadata was invalid.".to_string())?;
    let actual = sha256_digest_hex(digest);
    if actual == normalized {
        Ok(())
    } else {
        Err("Release checksum did not match the downloaded archive.".into())
    }
}

fn download_client() -> Result<reqwest::Client, String> {
    reqwest::Client::builder()
        .connect_timeout(DOWNLOAD_CONNECT_TIMEOUT)
        .read_timeout(DOWNLOAD_READ_TIMEOUT)
        .build()
        .map_err(|e| format!("Failed to prepare download client: {e}"))
}

fn content_range_total(headers: &HeaderMap) -> Option<u64> {
    let value = headers.get(CONTENT_RANGE)?.to_str().ok()?;
    let total = value.rsplit_once('/')?.1;
    if total == "*" {
        None
    } else {
        total.parse().ok()
    }
}

async fn sha256_file_digest(path: &Path) -> Result<Sha256, String> {
    let mut file = fs::File::open(path)
        .await
        .map_err(|e| format!("Failed to open download for verification: {e}"))?;
    let mut digest = Sha256::new();
    let mut buffer = vec![0_u8; 1024 * 1024];
    loop {
        let read = file
            .read(&mut buffer)
            .await
            .map_err(|e| format!("Failed to verify download: {e}"))?;
        if read == 0 {
            break;
        }
        digest.update(&buffer[..read]);
    }
    Ok(digest)
}

#[allow(clippy::too_many_arguments)]
async fn download_archive_with_resume(
    client: &reqwest::Client,
    url: &str,
    archive_path: &Path,
    expected_size: Option<u64>,
    expected_sha256: Option<&str>,
    install_dir: &str,
    state: &mut InstallerState,
    app: &AppHandle,
    step_id: SetupStepId,
    item_label: &str,
    progress_start: f64,
    progress_span: f64,
) -> Result<u64, String> {
    if let Some(parent) = archive_path.parent() {
        fs::create_dir_all(parent)
            .await
            .map_err(|e| format!("mkdir failed: {e}"))?;
    }

    let mut last_err = None;
    for attempt in 1..=DOWNLOAD_RETRY_ATTEMPTS {
        let mut existing_bytes = fs::metadata(archive_path)
            .await
            .map(|metadata| metadata.len())
            .unwrap_or(0);
        if expected_size
            .map(|size| existing_bytes > size)
            .unwrap_or(false)
        {
            let _ = fs::remove_file(archive_path).await;
            existing_bytes = 0;
        }
        if expected_size
            .map(|size| existing_bytes == size && size > 0)
            .unwrap_or(false)
        {
            if let Some(expected) = expected_sha256 {
                match sha256_file_digest(archive_path)
                    .await
                    .and_then(|digest| verify_sha256_digest(digest, expected))
                {
                    Ok(()) => return Ok(existing_bytes),
                    Err(_) => {
                        let _ = fs::remove_file(archive_path).await;
                        existing_bytes = 0;
                    }
                }
            } else {
                return Ok(existing_bytes);
            }
        }

        if existing_bytes > 0 {
            let detail = format!(
                "Resuming {item_label} from {}",
                format_bytes_compact(existing_bytes)
            );
            set_step_progress(state, app, &step_id, detail, None);
        }

        let mut request = client.get(url).header("User-Agent", "stella-launcher");
        if existing_bytes > 0 {
            request = request.header(RANGE, format!("bytes={existing_bytes}-"));
        }

        let resp = match request.send().await {
            Ok(resp) => resp,
            Err(err) => {
                last_err = Some(format!("{item_label} download failed: {err}"));
                log_install(
                    install_dir,
                    &format!("{item_label} download connection failed on attempt {attempt}: {err}"),
                )
                .await;
                if attempt < DOWNLOAD_RETRY_ATTEMPTS {
                    tokio::time::sleep(Duration::from_secs(attempt as u64)).await;
                    continue;
                }
                break;
            }
        };

        let status = resp.status();
        if status == reqwest::StatusCode::RANGE_NOT_SATISFIABLE {
            if expected_size
                .map(|size| existing_bytes == size)
                .unwrap_or(false)
            {
                if let Some(expected) = expected_sha256 {
                    let digest = sha256_file_digest(archive_path).await?;
                    verify_sha256_digest(digest, expected)?;
                }
                return Ok(existing_bytes);
            }
            let _ = fs::remove_file(archive_path).await;
            last_err = Some(format!("{item_label} download resume was rejected."));
            if attempt < DOWNLOAD_RETRY_ATTEMPTS {
                tokio::time::sleep(Duration::from_secs(attempt as u64)).await;
                continue;
            }
            break;
        }

        if !status.is_success() {
            return Err(format!("{item_label} download failed: HTTP {status}"));
        }

        let resuming = existing_bytes > 0 && status == reqwest::StatusCode::PARTIAL_CONTENT;
        if existing_bytes > 0 && !resuming {
            log_install(
                install_dir,
                &format!("{item_label} server did not resume; restarting download"),
            )
            .await;
            let _ = fs::remove_file(archive_path).await;
            existing_bytes = 0;
        }

        let response_total = if resuming {
            expected_size
                .or_else(|| content_range_total(resp.headers()))
                .or_else(|| resp.content_length().map(|length| existing_bytes + length))
        } else {
            resp.content_length().or(expected_size)
        };
        let mut downloaded = existing_bytes;
        let mut archive_file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .append(resuming)
            .truncate(!resuming)
            .open(archive_path)
            .await
            .map_err(|e| format!("Failed to prepare {item_label} download: {e}"))?;
        let mut stream = resp.bytes_stream();
        let mut last_emit = std::time::Instant::now()
            .checked_sub(Duration::from_secs(1))
            .unwrap_or_else(std::time::Instant::now);
        let mut attempt_err = None;

        while let Some(chunk) = stream.next().await {
            let chunk = match chunk {
                Ok(chunk) => chunk,
                Err(err) => {
                    attempt_err = Some(format!("{item_label} download failed: {err}"));
                    break;
                }
            };
            downloaded += chunk.len() as u64;
            if let Err(err) = archive_file.write_all(&chunk).await {
                attempt_err = Some(format!("Failed to write {item_label} download: {err}"));
                break;
            }

            if last_emit.elapsed() >= Duration::from_millis(300) {
                let detail = if let Some(total) = response_total {
                    format!(
                        "Downloading {item_label} {} of {}",
                        format_bytes_compact(downloaded),
                        format_bytes_compact(total)
                    )
                } else {
                    format!(
                        "Downloading {item_label} {}",
                        format_bytes_compact(downloaded)
                    )
                };
                let progress = response_total.filter(|total| *total > 0).map(|total| {
                    progress_start + ((downloaded as f64 / total as f64).min(1.0) * progress_span)
                });
                set_step_progress(state, app, &step_id, detail, progress);
                last_emit = std::time::Instant::now();
            }
        }

        if attempt_err.is_none() {
            if let Err(err) = archive_file.flush().await {
                attempt_err = Some(format!("Failed to finish {item_label} download: {err}"));
            }
        }
        drop(archive_file);

        if let Some(err) = attempt_err {
            last_err = Some(err.clone());
            log_install(
                install_dir,
                &format!(
                    "{item_label} download interrupted on attempt {attempt}; keeping {} for resume: {err}",
                    format_bytes_compact(downloaded)
                ),
            )
            .await;
            if attempt < DOWNLOAD_RETRY_ATTEMPTS {
                tokio::time::sleep(Duration::from_secs(attempt as u64)).await;
                continue;
            }
            break;
        }

        if expected_size.map(|size| downloaded < size).unwrap_or(false) {
            last_err = Some(format!(
                "{item_label} download ended early at {} of {}.",
                format_bytes_compact(downloaded),
                format_bytes_compact(expected_size.unwrap_or_default())
            ));
            if attempt < DOWNLOAD_RETRY_ATTEMPTS {
                tokio::time::sleep(Duration::from_secs(attempt as u64)).await;
                continue;
            }
            break;
        }

        if let Some(expected) = expected_sha256 {
            match sha256_file_digest(archive_path)
                .await
                .and_then(|digest| verify_sha256_digest(digest, expected))
            {
                Ok(()) => {}
                Err(err) => {
                    let _ = fs::remove_file(archive_path).await;
                    last_err = Some(err);
                    if attempt < DOWNLOAD_RETRY_ATTEMPTS {
                        tokio::time::sleep(Duration::from_secs(attempt as u64)).await;
                        continue;
                    }
                    break;
                }
            }
        }

        return Ok(downloaded);
    }

    Err(last_err.unwrap_or_else(|| format!("{item_label} download failed.")))
}

fn valid_release_commit(value: &str) -> bool {
    matches!(value.len(), 40 | 64) && value.chars().all(|char| char.is_ascii_hexdigit())
}

async fn resolve_r2_desktop_release(
    client: &reqwest::Client,
    install_dir: &str,
) -> Result<ResolvedDesktopRelease, String> {
    let manifest_url = desktop_release_manifest_url();
    log_install(
        install_dir,
        &format!("Resolving desktop release manifest: {manifest_url}"),
    )
    .await;
    let manifest_text = fetch_required_text(client, &manifest_url).await?;
    let manifest: DesktopDownloadManifest = serde_json::from_str(&manifest_text)
        .map_err(|e| format!("Desktop release manifest was invalid JSON: {e}"))?;
    if manifest.schema_version != 2 {
        return Err("Desktop release manifest schema is not supported.".into());
    }
    if manifest.tag.trim().is_empty() || !valid_release_commit(&manifest.commit) {
        return Err("Desktop release manifest did not identify a valid Git commit.".into());
    }
    let platform = desktop_platform_key();
    let platform_release =
        manifest.platforms.get(platform).cloned().ok_or_else(|| {
            format!("Desktop release manifest did not include platform {platform}.")
        })?;
    for required_kind in ["native-helpers", "stella-browser"] {
        if !platform_release
            .artifact_refs
            .iter()
            .any(|reference| reference.kind == required_kind && reference.platform == platform)
        {
            return Err(format!(
                "Desktop release manifest did not pin {required_kind} for {platform}."
            ));
        }
    }
    log_install(
        install_dir,
        &format!(
            "Resolved desktop release {} at {} for {platform}",
            manifest.tag, manifest.commit
        ),
    )
    .await;
    Ok(ResolvedDesktopRelease {
        tag: manifest.tag,
        commit: manifest.commit.to_ascii_lowercase(),
        platform: platform.to_string(),
        artifact_refs: platform_release.artifact_refs,
    })
}

async fn read_release_manifest_at(path: &Path) -> Result<DesktopReleaseManifest, String> {
    let raw = fs::read_to_string(path)
        .await
        .map_err(|e| format!("Failed to read release manifest: {e}"))?;
    let manifest = serde_json::from_str::<DesktopReleaseManifest>(&raw)
        .map_err(|e| format!("Release manifest was invalid JSON: {e}"))?;
    if manifest.schema_version != 1 {
        return Err("Release manifest schema is not supported.".into());
    }
    Ok(manifest)
}

async fn read_release_manifest(install_dir: &str) -> Result<DesktopReleaseManifest, String> {
    read_release_manifest_at(&release_manifest_of(install_dir)).await
}

// ── Git init for self-mod ───────────────────────────────────────────

fn install_git_identity(install_dir: &str) -> (String, String) {
    let mut digest = Sha256::new();
    digest.update(b"stella-install-git-identity-v1");
    digest.update(install_dir.as_bytes());
    for key in ["COMPUTERNAME", "USERDOMAIN", "USERNAME", "HOSTNAME", "USER"] {
        if let Ok(value) = std::env::var(key) {
            digest.update(key.as_bytes());
            digest.update(value.as_bytes());
        }
    }
    let identity = sha256_digest_hex(digest)
        .chars()
        .take(12)
        .collect::<String>();
    (
        format!("Stella Install {identity}"),
        format!("install-{identity}@stella.local"),
    )
}

fn git_config_value_missing(output: &std::process::Output) -> bool {
    !output.status.success() || String::from_utf8_lossy(&output.stdout).trim().is_empty()
}

/// Configure a private identity for self-mod commits in the cloned repository.
/// Fresh installs must already contain a valid clone; this never synthesizes
/// or repairs repository history.
async fn configure_cloned_git_identity(install_dir: &str) {
    let git_dir = Path::new(install_dir).join(".git");
    let Some(git) = available_git_runtime() else {
        return;
    };
    if !path_exists(&git_dir).await {
        return;
    }

    let git_bin = git.bin;
    let env = git.env;
    let cwd = PathBuf::from(install_dir);
    let (git_user_name, git_user_email) = install_git_identity(install_dir);

    let run_git = |args: Vec<String>| {
        let git_bin = git_bin.clone();
        let cwd = cwd.clone();
        let env = env.clone();
        async move {
            let mut cmd = Command::new(&git_bin);
            cmd.args(&args).current_dir(&cwd).envs(&env);
            #[cfg(target_os = "windows")]
            cmd.creation_flags(0x08000000);
            cmd.output().await
        }
    };

    let user_name_missing = run_git(vec!["config".into(), "--get".into(), "user.name".into()])
        .await
        .map(|output| git_config_value_missing(&output))
        .unwrap_or(true);
    if user_name_missing {
        let _ = run_git(vec!["config".into(), "user.name".into(), git_user_name]).await;
    }
    let user_email_missing = run_git(vec!["config".into(), "--get".into(), "user.email".into()])
        .await
        .map(|output| git_config_value_missing(&output))
        .unwrap_or(true);
    if user_email_missing {
        let _ = run_git(vec!["config".into(), "user.email".into(), git_user_email]).await;
    }
}

fn schedule_cloned_git_identity(install_dir: String) {
    tokio::spawn(async move {
        configure_cloned_git_identity(&install_dir).await;
    });
}

/// Remove `backend/` and `launcher/` directories left behind by
/// pre-split installs. Both moved out of the desktop tarball into
/// their own repos (`stella-backend`, `stella-launcher`); leaving the
/// stale copies in the install dir confuses the install-update agent
/// and bloats the working tree. Idempotent: missing dirs are a no-op.
async fn prune_legacy_split_dirs(install_dir: &str) {
    for legacy in ["backend", "launcher"] {
        let path = Path::new(install_dir).join(legacy);
        if path_exists(&path).await {
            let _ = fs::remove_dir_all(&path).await;
        }
    }
}

// ── Logging ─────────────────────────────────────────────────────────

async fn log_install(dir: &str, msg: &str) {
    let log_path = Path::new(dir).join("stella-install.log");
    let timestamp = chrono_now();
    let line = format!("[{timestamp}] {msg}\n");
    if let Ok(mut contents) = fs::read_to_string(&log_path).await {
        contents.push_str(&line);
        let _ = fs::write(&log_path, contents).await;
    } else {
        let _ = fs::create_dir_all(dir).await;
        let _ = fs::write(&log_path, &line).await;
    }
}

fn chrono_now() -> String {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    now.as_secs().to_string()
}

// ── Step infrastructure ─────────────────────────────────────────────

struct StepDef {
    id: SetupStepId,
    label: &'static str,
}

struct StepCheck {
    complete: bool,
    reason: Option<String>,
}

impl StepCheck {
    fn complete() -> Self {
        Self {
            complete: true,
            reason: None,
        }
    }

    fn incomplete(reason: impl Into<String>) -> Self {
        Self {
            complete: false,
            reason: Some(reason.into()),
        }
    }

    /// Mark a step incomplete without attaching a "reason" string. Use
    /// this when the step label alone conveys what's happening — adding
    /// a "<thing> is missing" reason during a fresh install is just
    /// noise that duplicates the pending status indicator.
    fn incomplete_silent() -> Self {
        Self {
            complete: false,
            reason: None,
        }
    }
}

fn build_step_defs() -> Vec<StepDef> {
    vec![
        StepDef {
            id: SetupStepId::Runtime,
            label: "Setting up",
        },
        StepDef {
            id: SetupStepId::Payload,
            label: "Downloading Stella",
        },
        StepDef {
            id: SetupStepId::Parakeet,
            label: "Preparing local dictation",
        },
        StepDef {
            id: SetupStepId::Finalize,
            label: "Finishing up",
        },
    ]
}

async fn check_step(id: &SetupStepId, state: &InstallerState) -> StepCheck {
    let dir = &state.install_path;
    match id {
        SetupStepId::Runtime => {
            if bun_on_path().await
                && available_git_runtime().is_some()
                && available_node_binary().is_some()
                && available_python_binary().is_some()
            {
                StepCheck::complete()
            } else {
                StepCheck::incomplete_silent()
            }
        }
        SetupStepId::Payload => payload_step_check(dir).await,
        SetupStepId::Parakeet => parakeet_step_check(dir).await,
        SetupStepId::Finalize => {
            if state.dev_mode || valid_install_manifest_exists(dir).await {
                StepCheck::complete()
            } else {
                StepCheck::incomplete_silent()
            }
        }
        _ => StepCheck::complete(),
    }
}

async fn payload_step_complete(dir: &str) -> bool {
    payload_step_check(dir).await.complete
}

async fn payload_step_check(dir: &str) -> StepCheck {
    if !path_exists(&node_modules_of(dir)).await {
        return StepCheck::incomplete_silent();
    }
    if !path_exists(&electron_dist_dir_of(dir)).await {
        return StepCheck::incomplete_silent();
    }
    if !looks_like_stella_source_tree(Path::new(dir)) {
        return StepCheck::incomplete("The selected folder is not a Stella desktop install.");
    }
    StepCheck::complete()
}

#[cfg(test)]
async fn parakeet_step_complete(dir: &str) -> bool {
    parakeet_step_check(dir).await.complete
}

async fn parakeet_step_check(dir: &str) -> StepCheck {
    // Local dictation is optional everywhere. Before the payload lands, keep the
    // step pending so install can run; after payload is present, never block
    // launch on a missing native helper or model.
    if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        if !path_exists(&parakeet_helper_of(dir)).await {
            return if payload_step_complete(dir).await {
                StepCheck::complete()
            } else {
                StepCheck::incomplete_silent()
            };
        }
        return if path_exists(&parakeet_cache_dir_of(dir).join("FluidAudio")).await
            || path_exists(&parakeet_cache_dir_of(dir).join("fluidaudio")).await
        {
            StepCheck::complete()
        } else {
            StepCheck::incomplete_silent()
        };
    }
    if parakeet_cpp_supported() {
        if !path_exists(&parakeet_cpp_helper_of(dir)).await {
            return if payload_step_complete(dir).await {
                StepCheck::complete()
            } else {
                StepCheck::incomplete_silent()
            };
        }
        return if parakeet_cpp_model_present(&parakeet_cpp_model_path_of(dir)).await {
            StepCheck::complete()
        } else {
            StepCheck::incomplete_silent()
        };
    }
    StepCheck::complete()
}

async fn install_step(
    id: &SetupStepId,
    state: &mut InstallerState,
    app: &AppHandle,
) -> Result<(), String> {
    let dir = state.install_path.clone();
    match id {
        SetupStepId::Runtime => {
            if !bun_on_path().await && !install_bun_globally().await {
                return Err(
                    "Failed to install Bun runtime. Check your internet connection.".into(),
                );
            }
            let client = download_client()?;
            prepare_git_runtime(&client, &dir, state, app, SetupStepId::Runtime).await?;
            ensure_node_runtime(&client, &dir, state, app).await?;
            ensure_python_runtime(&client, &dir, state, app).await?;
            Ok(())
        }
        SetupStepId::Payload => {
            let _ = fs::create_dir_all(&dir).await;
            let release = download_and_clone_release(&dir, state, app).await?;
            write_default_env_file(&dir).await?;
            install_release_artifacts(&dir, &release, state, app).await?;
            set_step_progress(
                state,
                app,
                &SetupStepId::Payload,
                "Installing Stella's dependencies",
                Some(0.8),
            );
            install_payload_dependencies(&dir, state, app).await?;
            if available_git_runtime().is_none() {
                return Err("Stella's Git runtime was missing after dependency setup.".into());
            }
            Ok(())
        }
        SetupStepId::Parakeet => {
            if let Err(err) = ensure_parakeet_model_downloaded(&dir).await {
                // Log for debugging, but don't pop a banner — local dictation
                // is optional and the failure isn't actionable for the user.
                log_install(&dir, &format!("Parakeet install warning: {err}")).await;
            }
            Ok(())
        }
        SetupStepId::Finalize => {
            if let Err(err) = ensure_ripgrep_provisioned(&dir).await {
                log_install(&dir, &format!("Ripgrep install warning: {err}")).await;
            }
            let script_path = write_launch_script(&dir, state.low_resource_mode).await;
            let release_manifest = read_release_manifest(&dir).await.ok();

            let manifest = Manifest {
                version: env!("CARGO_PKG_VERSION").into(),
                desktop_release_tag: release_manifest
                    .as_ref()
                    .map(|manifest| manifest.tag.clone()),
                desktop_release_commit: release_manifest
                    .as_ref()
                    .and_then(|manifest| manifest.commit.clone()),
                platform: std::env::consts::OS.into(),
                installed_at: chrono_now(),
                install_path: dir.clone(),
                launch_script: script_path,
                shortcuts: HashMap::new(),
            };

            write_install_manifest_atomic(&manifest_of(&dir), &manifest).await?;

            schedule_cloned_git_identity(dir.clone());

            write_registry(&manifest).await;
            Ok(())
        }
        _ => Ok(()),
    }
}

// ── State management ────────────────────────────────────────────────

fn sync_step_list(state: &mut InstallerState) {
    let defs = build_step_defs();
    let mut new_steps = Vec::new();
    for def in &defs {
        if let Some(existing) = state.steps.iter().find(|s| s.id == def.id) {
            new_steps.push(existing.clone());
        } else {
            new_steps.push(SetupStep {
                id: def.id.clone(),
                label: def.label.to_string(),
                status: SetupStepStatus::Pending,
                detail: None,
                progress: None,
            });
        }
    }
    state.steps = new_steps;
}

async fn refresh_derived(state: &mut InstallerState, ctx: &InstallerContext) {
    let avail = disk::available_bytes(&state.install_path).await;

    state.disk = DiskInfo {
        required_bytes: ctx.required_bytes,
        available_bytes: avail,
        used_bytes: 0, // Skip expensive dir walk
        enough_space: avail.map_or(true, |a| a >= ctx.required_bytes),
    };

    state.install_path_error = location_error(&state.install_path);

    state.can_launch = if state.dev_mode {
        looks_like_stella_source_tree(Path::new(&state.install_path))
            && path_exists(&node_modules_of(&state.install_path)).await
    } else {
        valid_install_manifest_exists(&state.install_path).await
            && payload_step_complete(&state.install_path).await
    };
    state.warning_message = None;
}

fn emit_state_fast(state: &InstallerState, app: &AppHandle) {
    let _ = app.emit(
        "installer-state-update",
        serde_json::json!({ "state": state }),
    );
}

async fn emit_state_full(state: &mut InstallerState, ctx: &InstallerContext, app: &AppHandle) {
    refresh_derived(state, ctx).await;
    let _ = app.emit(
        "installer-state-update",
        serde_json::json!({ "state": &*state }),
    );
}

// ── Public API ──────────────────────────────────────────────────────

pub fn create_context(
    default_install_path: String,
    settings_file_path: PathBuf,
    dev_mode: bool,
) -> InstallerContext {
    InstallerContext {
        default_install_path,
        settings_file_path,
        required_bytes: ESTIMATED_INSTALL_BYTES,
        dev_mode,
    }
}

pub async fn create_initial_state(ctx: &InstallerContext) -> InstallerState {
    let settings = read_settings(ctx).await;
    let install_path = if ctx.dev_mode {
        norm(&ctx.default_install_path)
    } else {
        resolve_install_path(
            settings
                .installed_path
                .as_deref()
                .or(settings.install_path.as_deref())
                .unwrap_or(&ctx.default_install_path),
        )
    };

    let mut state = InstallerState {
        steps: vec![],
        phase: InstallerPhase::Checking,
        error_message: None,
        warning_message: None,
        install_path,
        default_install_path: ctx.default_install_path.clone(),
        dev_mode: ctx.dev_mode,
        install_path_locked: ctx.dev_mode,
        install_path_error: None,
        run_after_install: settings.run_after_install.unwrap_or(true),
        low_resource_mode: settings.low_resource_mode,
        can_launch: false,
        installed: false,
        launcher_update: LauncherUpdateInfo {
            current_version: env!("CARGO_PKG_VERSION").to_string(),
            ..LauncherUpdateInfo::default()
        },
        disk: DiskInfo {
            required_bytes: ctx.required_bytes,
            available_bytes: None,
            used_bytes: 0,
            enough_space: true,
        },
    };

    refresh_derived(&mut state, ctx).await;
    sync_step_list(&mut state);
    state
}

pub async fn set_install_path(
    state: &mut InstallerState,
    ctx: &InstallerContext,
    install_path: &str,
) {
    if ctx.dev_mode {
        state.install_path = norm(&ctx.default_install_path);
        state.error_message = None;
        state.warning_message = None;
        return;
    }
    state.install_path = resolve_install_path(install_path);
    state.error_message = None;
    state.warning_message = None;
    write_settings(ctx, state).await;
}

pub async fn set_run_after_install(
    state: &mut InstallerState,
    ctx: &InstallerContext,
    value: bool,
) {
    if ctx.dev_mode {
        state.run_after_install = true;
        return;
    }
    state.run_after_install = value;
    write_settings(ctx, state).await;
}

pub async fn set_low_resource_mode(
    state: &mut InstallerState,
    ctx: &InstallerContext,
    value: bool,
) {
    if ctx.dev_mode {
        state.low_resource_mode = false;
        return;
    }
    state.low_resource_mode = value;
    let _ = write_launch_script(&state.install_path, state.low_resource_mode).await;
    write_settings(ctx, state).await;
}

pub async fn check_all(state: &mut InstallerState, ctx: &InstallerContext, app: &AppHandle) {
    state.phase = InstallerPhase::Checking;
    state.error_message = None;
    state.warning_message = None;
    sync_step_list(state);
    emit_state_fast(state, app);

    let defs = build_step_defs();
    let mut all_done = true;

    for def in &defs {
        let check = check_step(&def.id, state).await;

        if let Some(step) = state.steps.iter_mut().find(|s| s.id == def.id) {
            step.status = if check.complete {
                SetupStepStatus::Skipped
            } else {
                SetupStepStatus::Pending
            };
            step.detail = check.reason;
            step.progress = None;
        }

        if !check.complete {
            all_done = false;
        }
    }

    state.installed = all_done;
    state.phase = if all_done {
        InstallerPhase::Complete
    } else {
        InstallerPhase::Ready
    };
    emit_state_full(state, ctx, app).await;
}

pub async fn install_all(
    state: &mut InstallerState,
    ctx: &InstallerContext,
    app: &AppHandle,
) -> Result<(), String> {
    refresh_derived(state, ctx).await;

    if let Some(err) = &state.install_path_error {
        let msg = err.clone();
        state.phase = InstallerPhase::Error;
        state.error_message = Some(msg.clone());
        emit_state_fast(state, app);
        return Err(msg);
    }

    if !state.disk.enough_space {
        let msg = "Not enough free disk space.".to_string();
        state.phase = InstallerPhase::Error;
        state.error_message = Some(msg.clone());
        emit_state_fast(state, app);
        return Err(msg);
    }

    sync_step_list(state);
    state.phase = InstallerPhase::Installing;
    state.error_message = None;
    state.warning_message = None;
    emit_state_fast(state, app);

    let defs = build_step_defs();

    for def in &defs {
        let check = check_step(&def.id, state).await;
        if check.complete {
            if let Some(step) = state.steps.iter_mut().find(|s| s.id == def.id) {
                step.status = SetupStepStatus::Skipped;
                step.detail = None;
                step.progress = None;
            }
            emit_state_fast(state, app);
            continue;
        }

        if let Some(step) = state.steps.iter_mut().find(|s| s.id == def.id) {
            step.status = SetupStepStatus::Installing;
            step.detail = check.reason.or_else(|| Some(def.label.to_string()));
            step.progress = None;
        }
        emit_state_fast(state, app);

        let result = install_step(&def.id, state, app).await;

        if let Err(err) = result {
            log_install(
                &state.install_path,
                &format!("Step '{}' failed: {}", def.label, err),
            )
            .await;
            if let Some(step) = state.steps.iter_mut().find(|s| s.id == def.id) {
                step.status = SetupStepStatus::Error;
                step.detail = Some(err.clone());
            }
            state.phase = InstallerPhase::Error;
            state.error_message = Some(err.clone());
            emit_state_fast(state, app);
            return Err(err);
        }

        if let Some(step) = state.steps.iter_mut().find(|s| s.id == def.id) {
            step.status = SetupStepStatus::Done;
            step.progress = None;
        }
        emit_state_fast(state, app);
    }

    state.installed = true;
    state.phase = InstallerPhase::Complete;
    write_settings(ctx, state).await;
    emit_state_full(state, ctx, app).await;

    Ok(())
}

pub async fn get_launch_info(state: &InstallerState) -> Option<LaunchInfo> {
    let dir = &state.install_path;
    if !path_exists(&package_json_of(dir)).await {
        return None;
    }

    prune_legacy_split_dirs(dir).await;
    schedule_cloned_git_identity(dir.clone());
    if !ripgrep_private_binary_exists().await {
        let _ = ensure_ripgrep_provisioned(dir).await;
    }

    let mut env = runtime_launch_env(dir);
    if let Ok(exe) = std::env::current_exe() {
        env.insert(
            "STELLA_LAUNCHER_PROTECTED_STORAGE_BIN".into(),
            exe.to_string_lossy().to_string(),
        );
    }
    Some(LaunchInfo {
        command: desktop_launch_command(state.low_resource_mode),
        cwd: dir.clone(),
        env,
    })
}

pub async fn uninstall(state: &mut InstallerState) -> Result<(), String> {
    if path_exists_str(&state.install_path).await {
        if !is_uninstallable_install_path(&state.install_path) {
            let msg =
                "Refusing to remove a folder that does not look like a Stella install.".to_string();
            state.phase = InstallerPhase::Error;
            state.error_message = Some(msg.clone());
            return Err(msg);
        }
        remove_install_files(&state.install_path).await?;
    }

    remove_registry().await;

    state.installed = false;
    state.phase = InstallerPhase::Ready;
    state.error_message = None;
    state.steps.clear();
    state.warning_message = None;
    sync_step_list(state);

    Ok(())
}

/// Path to the durable Stella home directory (`~/.stella`). The desktop
/// runtime treats this folder as the source of truth for chats, memories,
/// credentials, the skill catalog, the SQLite database — every artifact
/// that should survive an upgrade. "Erase everything" is intentionally
/// destructive and must wipe it alongside the install root.
fn stella_data_dir() -> PathBuf {
    home_dir().join(".stella")
}

/// Refuse to nuke anything that doesn't look like our home directory.
/// In practice this means the path must sit directly inside the user's
/// home as the literal `.stella` folder. Any drift (test environments
/// without a real `$HOME`, a manually relocated home, etc.) bails out
/// instead of risking unrelated user data.
fn is_erasable_stella_data_dir(path: &Path) -> bool {
    if !path.is_dir() {
        return false;
    }
    if path.file_name().and_then(|n| n.to_str()) != Some(".stella") {
        return false;
    }
    let Some(parent) = path.parent() else {
        return false;
    };
    let expected_parent = home_dir();
    if expected_parent.as_os_str().is_empty() {
        return false;
    }
    match (parent.canonicalize(), expected_parent.canonicalize()) {
        (Ok(a), Ok(b)) => a == b,
        _ => parent == expected_parent,
    }
}

/// Wipe the entire Stella install directory AND the durable home
/// (`~/.stella`). This is the user-visible "Erase everything" surface
/// and is intentionally destructive: chats, memories, settings, mods,
/// agent edits, credentials all go.
pub async fn full_reset(state: &mut InstallerState) -> Result<(), String> {
    if path_exists_str(&state.install_path).await {
        if !is_uninstallable_install_path(&state.install_path) {
            let msg =
                "Refusing to erase a folder that does not look like a Stella install.".to_string();
            state.phase = InstallerPhase::Error;
            state.error_message = Some(msg.clone());
            return Err(msg);
        }
        fs::remove_dir_all(&state.install_path)
            .await
            .map_err(|e| format!("Failed to erase Stella folder: {e}"))?;
    }

    let home = stella_data_dir();
    if path_exists(&home).await {
        if !is_erasable_stella_data_dir(&home) {
            let msg = "Refusing to erase a folder that does not look like ~/.stella.".to_string();
            state.phase = InstallerPhase::Error;
            state.error_message = Some(msg.clone());
            return Err(msg);
        }
        fs::remove_dir_all(&home)
            .await
            .map_err(|e| format!("Failed to erase Stella home: {e}"))?;
    }

    remove_registry().await;

    state.installed = false;
    state.phase = InstallerPhase::Ready;
    state.error_message = None;
    state.steps.clear();
    state.warning_message = None;
    sync_step_list(state);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct TestDir {
        path: PathBuf,
    }

    impl TestDir {
        fn new(label: &str) -> Self {
            let unique = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos();
            let path = std::env::temp_dir().join(format!("stella-launcher-{label}-{unique}"));
            fs::create_dir_all(&path).expect("create temp dir");
            Self { path }
        }
    }

    impl Drop for TestDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    fn write_install_shape(path: &Path) {
        fs::create_dir_all(path.join("desktop")).expect("create desktop dir");
        fs::create_dir_all(path.join("runtime")).expect("create runtime dir");
        fs::write(path.join("package.json"), r#"{"name":"stella"}"#).expect("write package");
    }

    fn write_dependency_shape(path: &Path) {
        fs::create_dir_all(path.join("node_modules").join("electron").join("dist"))
            .expect("create bundled dependencies");
    }

    #[test]
    fn launch_env_prepends_stella_private_bin() {
        let dir = TestDir::new("launch-env-bin");
        let env = runtime_launch_env(&dir.path.to_string_lossy());
        let path_value = env.get("PATH").expect("PATH env");
        let first_entry = path_value
            .split(path_separator())
            .next()
            .expect("first PATH entry");

        assert_eq!(
            first_entry,
            stella_private_bin_dir().to_string_lossy().as_ref()
        );
        assert_eq!(
            env.get("STELLA_DATA_DIR").map(String::as_str),
            Some(stella_data_dir().to_string_lossy().as_ref())
        );
    }

    fn write_release_manifest(path: &Path, files: &[&str]) {
        write_release_manifest_with_tag(path, "desktop-v0.0.1", files);
    }

    fn write_release_manifest_with_tag(path: &Path, tag: &str, files: &[&str]) {
        let files_json = files
            .iter()
            .map(|file| format!(r#""{file}":{{"sha256":"abc"}}"#))
            .collect::<Vec<_>>()
            .join(",");
        fs::write(
            path.join(RELEASE_MANIFEST),
            format!(r#"{{"schemaVersion":1,"tag":"{tag}","files":{{{files_json}}}}}"#),
        )
        .expect("write release manifest");
    }

    fn write_native_helpers_shape(path: &Path) {
        let install_dir = path.to_string_lossy();
        let helpers_dir = native_helpers_dir_of(&install_dir);
        fs::create_dir_all(&helpers_dir).expect("create native helpers dir");
        let sentinel = if cfg!(target_os = "windows") {
            helpers_dir.join("window_info.exe")
        } else {
            helpers_dir.join("window_info")
        };
        fs::write(sentinel, "").expect("write native helper sentinel");
    }

    fn write_generic_package_shape(path: &Path) {
        fs::write(path.join("package.json"), r#"{"name":"other-app"}"#).expect("write package");
    }

    #[test]
    fn resolve_install_path_adds_stella_folder_for_parent_paths() {
        let dir = TestDir::new("parent");
        let resolved = resolve_install_path(&dir.path.to_string_lossy());
        let resolved_path = PathBuf::from(&resolved);
        assert_eq!(
            resolved_path.file_name().and_then(|value| value.to_str()),
            Some(INSTALL_DIR_NAME)
        );
        assert_eq!(
            norm(
                &resolved_path
                    .parent()
                    .unwrap_or(Path::new(""))
                    .to_string_lossy()
            ),
            norm(&dir.path.to_string_lossy())
        );
    }

    #[test]
    fn resolve_install_path_preserves_existing_install_dirs() {
        let dir = TestDir::new("existing-install");
        write_install_shape(&dir.path);

        let resolved = resolve_install_path(&dir.path.to_string_lossy());
        assert_eq!(resolved, norm(&dir.path.to_string_lossy()));
    }

    #[test]
    fn location_error_rejects_nonempty_unmanaged_dirs() {
        let dir = TestDir::new("unmanaged");
        fs::write(dir.path.join("notes.txt"), "hello\n").expect("write unmanaged file");

        let error = location_error(&dir.path.to_string_lossy()).expect("expected location error");
        assert!(error.contains("own"));
        assert!(error.contains(INSTALL_DIR_NAME));
    }

    #[test]
    fn location_error_rejects_generic_package_dirs() {
        let dir = TestDir::new("generic-package");
        write_generic_package_shape(&dir.path);

        let error = location_error(&dir.path.to_string_lossy()).expect("expected location error");
        assert!(error.contains("own"));
        assert!(error.contains(INSTALL_DIR_NAME));
    }

    #[test]
    fn location_error_rejects_state_only_install_dirs() {
        let dir = TestDir::new("state-only");
        fs::create_dir_all(dir.path.join("state")).expect("create state dir");
        fs::write(dir.path.join("state").join("stella.sqlite"), "db").expect("write state file");

        assert!(location_error(&dir.path.to_string_lossy()).is_some());
    }

    #[test]
    fn location_error_rejects_state_only_install_dirs_with_benign_leftovers() {
        let dir = TestDir::new("state-only-leftovers");
        fs::create_dir_all(dir.path.join("state")).expect("create state dir");
        fs::write(dir.path.join("state").join("stella.sqlite"), "db").expect("write state file");
        fs::write(dir.path.join(".DS_Store"), "").expect("write ds store");
        fs::write(dir.path.join("stella-install.log"), "log").expect("write log");
        fs::write(dir.path.join(".stella-browser-download"), "")
            .expect("write temp browser download");

        assert!(location_error(&dir.path.to_string_lossy()).is_some());
    }

    #[test]
    fn location_error_allows_partial_launcher_download_dirs() {
        let dir = TestDir::new("partial-download");
        fs::write(dir.path.join("stella-install.log"), "log").expect("write log");
        fs::write(
            dir.path.join(".stella-native-helpers-download.tar.zst"),
            "partial",
        )
        .expect("write partial helpers archive");

        assert_eq!(location_error(&dir.path.to_string_lossy()), None);
    }

    #[test]
    fn location_error_allows_interrupted_clone_dirs() {
        let dir = TestDir::new("partial-clone");
        fs::write(dir.path.join("stella-install.log"), "log").expect("write log");
        let clone_dir = dir.path.join(".stella-source-clone");
        fs::create_dir_all(clone_dir.join(".git")).expect("create partial clone");
        fs::write(
            clone_dir.join(".git").join("HEAD"),
            "ref: refs/heads/master\n",
        )
        .expect("write partial clone head");

        assert_eq!(location_error(&dir.path.to_string_lossy()), None);
        assert!(is_uninstallable_install_path(&dir.path.to_string_lossy()));
    }

    #[test]
    fn uninstallable_install_path_requires_stella_shape() {
        let dir = TestDir::new("uninstallable");
        assert!(!is_uninstallable_install_path(&dir.path.to_string_lossy()));

        write_install_shape(&dir.path);
        assert!(is_uninstallable_install_path(&dir.path.to_string_lossy()));
    }

    #[test]
    fn uninstallable_install_path_rejects_generic_package_dirs() {
        let dir = TestDir::new("generic-uninstallable");
        write_generic_package_shape(&dir.path);

        assert!(!is_uninstallable_install_path(&dir.path.to_string_lossy()));
    }

    #[test]
    fn uninstallable_install_path_rejects_state_only_stella_dirs() {
        let dir = TestDir::new("uninstallable-state-only");
        fs::create_dir_all(dir.path.join("state")).expect("create state dir");
        fs::write(dir.path.join("state").join("stella.sqlite"), "db").expect("write state file");

        assert!(!is_uninstallable_install_path(&dir.path.to_string_lossy()));
    }

    #[test]
    fn uninstallable_install_path_rejects_state_only_stella_dirs_with_benign_leftovers() {
        let dir = TestDir::new("uninstallable-state-only-leftovers");
        fs::create_dir_all(dir.path.join("state")).expect("create state dir");
        fs::write(dir.path.join("state").join("stella.sqlite"), "db").expect("write state file");
        fs::write(dir.path.join(".DS_Store"), "").expect("write ds store");
        fs::write(dir.path.join("stella-install.log"), "log").expect("write log");
        fs::write(dir.path.join(".stella-browser-download"), "")
            .expect("write temp browser download");

        assert!(!is_uninstallable_install_path(&dir.path.to_string_lossy()));
    }

    #[test]
    fn uninstallable_install_path_allows_partial_launcher_download_dirs() {
        let dir = TestDir::new("uninstallable-partial-download");
        fs::write(dir.path.join("stella-install.log"), "log").expect("write log");
        fs::write(
            dir.path.join(".stella-native-helpers-download.tar.zst"),
            "partial",
        )
        .expect("write partial helpers archive");

        assert!(is_uninstallable_install_path(&dir.path.to_string_lossy()));
    }

    #[test]
    fn erasable_stella_data_dir_requires_dot_stella_inside_real_home() {
        // The literal `~/.stella` is the only path the launcher should ever
        // wipe — anything else (a sibling folder, an arbitrary temp dir,
        // even `~/.stella-archive`) must be refused.
        let home = home_dir();
        if home.as_os_str().is_empty() {
            return;
        }

        assert!(!is_erasable_stella_data_dir(Path::new("/")));
        assert!(!is_erasable_stella_data_dir(&home));
        assert!(!is_erasable_stella_data_dir(&home.join(".stella-archive")));

        let dir = TestDir::new("erasable-home-wrong-parent");
        let nested = dir.path.join(".stella");
        fs::create_dir_all(&nested).expect("create nested .stella");
        // Right name, wrong parent → refused.
        assert!(!is_erasable_stella_data_dir(&nested));
    }

    #[test]
    fn erasable_stella_data_dir_rejects_missing_or_file_paths() {
        let dir = TestDir::new("erasable-home-missing");
        assert!(!is_erasable_stella_data_dir(&dir.path.join(".stella")));

        let file_path = dir.path.join(".stella");
        fs::write(&file_path, "not a dir").expect("write sentinel");
        assert!(!is_erasable_stella_data_dir(&file_path));
    }

    #[test]
    fn launch_env_includes_private_and_bun_bins() {
        let dir = TestDir::new("launch-env");
        let env = runtime_launch_env(&dir.path.to_string_lossy());
        let path = env.get("PATH").expect("PATH env");
        let entries = path.split(path_separator()).collect::<Vec<_>>();
        assert_eq!(
            entries.first().copied(),
            Some(stella_private_bin_dir().to_string_lossy().as_ref())
        );
        assert!(entries.contains(&bun_bin_dir().to_string_lossy().as_ref()));
    }

    #[test]
    fn content_range_total_parses_known_totals() {
        let mut headers = HeaderMap::new();
        headers.insert(CONTENT_RANGE, "bytes 100-199/1234".parse().unwrap());

        assert_eq!(content_range_total(&headers), Some(1234));
    }

    #[test]
    fn content_range_total_ignores_unknown_totals() {
        let mut headers = HeaderMap::new();
        headers.insert(CONTENT_RANGE, "bytes 100-199/*".parse().unwrap());

        assert_eq!(content_range_total(&headers), None);
    }

    #[test]
    fn managed_git_manifest_resolves_checksum_pinned_platform_asset() {
        let platform = managed_runtime_platform_key().expect("supported test platform");
        let file_name = format!("stella-git-{platform}.tar.gz");
        let raw = format!(
            r#"{{
                "schemaVersion": 1,
                "version": "{MANAGED_GIT_VERSION}",
                "assets": {{
                    "{platform}": {{
                        "fileName": "{file_name}",
                        "url": "https://cdn.test/git-runtime/objects/runtime.tar.gz",
                        "sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                        "size": 123
                    }}
                }}
            }}"#
        );
        let manifest =
            serde_json::from_str::<ManagedGitManifest>(&raw).expect("managed Git manifest");
        let asset = resolve_managed_git_asset(manifest).expect("managed Git asset");

        assert_eq!(asset.file_name, file_name);
        assert!(asset.url.starts_with("https://"));
        assert_eq!(asset.sha256.len(), 64);
        assert!(asset.sha256.chars().all(|char| char.is_ascii_hexdigit()));
        assert_eq!(asset.size, 123);
        assert!(managed_git_archive_path(&asset).ends_with(&asset.file_name));
        assert!(
            git_runtime_manifest_url().ends_with(&format!("/{MANAGED_GIT_VERSION}/manifest.json"))
        );
    }

    #[test]
    fn managed_node_asset_is_checksum_pinned() {
        let asset = managed_node_asset().expect("supported test platform");
        assert!(asset
            .file_name
            .starts_with(&format!("node-v{MANAGED_NODE_VERSION}-")));
        assert!(asset.url.ends_with(asset.file_name));
        assert_eq!(asset.sha256.len(), 64);
        assert!(asset.sha256.chars().all(|char| char.is_ascii_hexdigit()));
        assert!(managed_node_archive_path()
            .expect("managed Node archive path")
            .ends_with(asset.file_name));
    }

    #[test]
    fn identity_setup_never_synthesizes_missing_git_history() {
        let dir = TestDir::new("missing-clone-history");

        tauri::async_runtime::block_on(configure_cloned_git_identity(&dir.path.to_string_lossy()));

        assert!(!dir.path.join(".git").exists());
    }

    #[test]
    fn desktop_download_manifest_parses_clone_and_artifact_pins() {
        let platform = desktop_platform_key();
        let raw = format!(
            r#"{{
                "schemaVersion": 2,
                "tag": "desktop-v0.0.447",
                "commit": "d38ddd8b2ef51bca13056bbddc42d55312371760",
                "platforms": {{
                    "{platform}": {{
                        "artifactRefs": [
                            {{
                                "kind": "native-helpers",
                                "platform": "{platform}",
                                "asset": {{
                                    "url": "https://example.test/native.tar.zst",
                                    "sha256": "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                                    "sizeBytes": 456
                                }}
                            }},
                            {{
                                "kind": "stella-browser",
                                "platform": "{platform}",
                                "asset": {{
                                    "url": "https://example.test/stella-browser",
                                    "sha256": "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
                                    "sizeBytes": 789
                                }}
                            }}
                        ]
                    }}
                }}
            }}"#
        );
        let manifest =
            serde_json::from_str::<DesktopDownloadManifest>(&raw).expect("desktop manifest");
        let platform_release = manifest.platforms.get(platform).expect("platform release");

        assert!(valid_release_commit(&manifest.commit));
        assert_eq!(platform_release.artifact_refs.len(), 2);
        assert_eq!(platform_release.artifact_refs[0].asset.size_bytes, 456);
        assert_eq!(
            validate_pinned_artifact(&platform_release.artifact_refs[1]).as_deref(),
            Ok("cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
        );
    }

    #[test]
    fn browser_revision_is_recovered_from_immutable_artifact_url() {
        assert_eq!(
            artifact_revision_from_url(
                "https://cdn.test/stella-browser/b62793bb4474d6d6c2d363f92e8a960432ef1edf/darwin-arm64/stella-browser",
                "stella-browser",
            )
            .as_deref(),
            Some("b62793bb4474d6d6c2d363f92e8a960432ef1edf")
        );
    }

    #[test]
    fn cloned_release_manifest_records_exact_upstream_commit() {
        let dir = TestDir::new("cloned-release-manifest");
        let release = ResolvedDesktopRelease {
            tag: "desktop-v0.0.447".into(),
            commit: "d38ddd8b2ef51bca13056bbddc42d55312371760".into(),
            platform: desktop_platform_key().into(),
            artifact_refs: Vec::new(),
        };

        tauri::async_runtime::block_on(write_cloned_release_manifest(
            &dir.path.to_string_lossy(),
            &release,
        ))
        .expect("write cloned release manifest");
        let raw = fs::read_to_string(dir.path.join(RELEASE_MANIFEST)).expect("read manifest");
        let parsed = serde_json::from_str::<serde_json::Value>(&raw).expect("parse manifest");

        assert_eq!(parsed["commit"], release.commit);
        assert_eq!(parsed["tag"], release.tag);
        assert!(parsed.get("bundledDependencies").is_none());
        assert!(parsed.get("bundledNativeHelpers").is_none());
        assert_eq!(parsed["files"], serde_json::json!({}));
    }

    #[test]
    fn payload_completion_rejects_missing_electron_binary() {
        let dir = TestDir::new("missing-electron");
        write_install_shape(&dir.path);
        fs::create_dir_all(dir.path.join("node_modules")).expect("create node_modules");

        let check = tauri::async_runtime::block_on(payload_step_check(&dir.path.to_string_lossy()));

        // Pre-install state is silent — the step label conveys the status
        // and a "binary is missing" detail string was just noise.
        assert!(!check.complete);
        assert_eq!(check.reason, None);
    }

    #[test]
    fn payload_completion_accepts_stale_or_ahead_release_manifest() {
        let dir = TestDir::new("stale-release-manifest");
        write_install_shape(&dir.path);
        write_dependency_shape(&dir.path);
        write_release_manifest(&dir.path, &["desktop/package.json", "runtime/missing.txt"]);
        fs::write(dir.path.join("desktop").join("package.json"), "{}").expect("write desktop file");

        let check = tauri::async_runtime::block_on(payload_step_check(&dir.path.to_string_lossy()));

        assert!(check.complete);
        assert_eq!(check.reason, None);
    }

    #[test]
    fn payload_completion_accepts_manifest_files_and_dependencies() {
        let dir = TestDir::new("complete-payload");
        write_install_shape(&dir.path);
        write_dependency_shape(&dir.path);
        fs::write(dir.path.join("desktop").join("package.json"), "{}").expect("write desktop file");
        fs::write(dir.path.join("runtime").join("package.json"), "{}").expect("write runtime file");
        write_release_manifest(&dir.path, &["desktop/package.json", "runtime/package.json"]);

        let complete =
            tauri::async_runtime::block_on(payload_step_complete(&dir.path.to_string_lossy()));

        assert!(complete);
    }

    #[test]
    fn parakeet_step_stays_pending_before_payload_is_installed() {
        let dir = TestDir::new("parakeet-before-payload");
        fs::create_dir_all(dir.path.join("state")).expect("create state dir");

        let complete =
            tauri::async_runtime::block_on(parakeet_step_complete(&dir.path.to_string_lossy()));

        // The Parakeet step stays pending before the payload lands on every
        // platform that ships a local dictation engine (Apple Silicon CoreML or
        // parakeet.cpp on Windows / Intel macOS); elsewhere it is a no-op.
        let parakeet_platform =
            cfg!(all(target_os = "macos", target_arch = "aarch64")) || parakeet_cpp_supported();
        assert_eq!(complete, !parakeet_platform);
    }

    #[test]
    fn parakeet_step_skips_missing_helper_after_payload_is_installed() {
        let dir = TestDir::new("parakeet-no-helper");
        write_install_shape(&dir.path);
        write_dependency_shape(&dir.path);
        fs::write(dir.path.join("desktop").join("package.json"), "{}").expect("write desktop file");
        fs::write(dir.path.join("runtime").join("package.json"), "{}").expect("write runtime file");
        write_release_manifest(&dir.path, &["desktop/package.json", "runtime/package.json"]);
        write_native_helpers_shape(&dir.path);

        let complete =
            tauri::async_runtime::block_on(parakeet_step_complete(&dir.path.to_string_lossy()));

        assert!(complete);
    }

    #[test]
    fn remove_install_files_removes_install_root() {
        let dir = TestDir::new("remove-install");
        write_install_shape(&dir.path);
        fs::create_dir_all(dir.path.join("state")).expect("create state dir");
        fs::write(dir.path.join("state").join("stella.sqlite"), "db").expect("write state file");
        fs::write(dir.path.join("launch.sh"), "#!/bin/sh\n").expect("write launch script");

        tauri::async_runtime::block_on(remove_install_files(&dir.path.to_string_lossy()))
            .expect("remove install files");

        assert!(!dir.path.exists());
        assert!(!dir.path.join("desktop").exists());
        assert!(!dir.path.join("runtime").exists());
        assert!(!dir.path.join("package.json").exists());
        assert!(!dir.path.join("launch.sh").exists());
    }
}
