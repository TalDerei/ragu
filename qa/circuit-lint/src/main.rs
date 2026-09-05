use std::{
    env, fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

use ragu_circuit_lint::analyze_source;

fn main() -> ExitCode {
    match run() {
        Ok(success) => ExitCode::from(u8::from(!success)),
        Err(error) => {
            eprintln!("ragu-circuit-lint: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<bool, String> {
    let mut root = env::current_dir().map_err(|error| error.to_string())?;
    let mut deny_advisories = false;
    let mut requested = Vec::new();
    let mut arguments = env::args().skip(1);
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--root" => {
                let path = arguments
                    .next()
                    .ok_or_else(|| "--root requires a path".to_owned())?;
                root = PathBuf::from(path);
            }
            "--deny-advisories" => deny_advisories = true,
            "--help" | "-h" => {
                println!(
                    "Usage: ragu-circuit-lint [--root PATH] [--deny-advisories] [PATH ...]\n\
                     Parses production Rust source without compiling or executing it.\n\
                     PATH arguments are resolved relative to --root."
                );
                return Ok(true);
            }
            argument if argument.starts_with('-') => {
                return Err(format!("unknown option `{argument}`"));
            }
            path => requested.push(PathBuf::from(path)),
        }
    }

    let roots = if requested.is_empty() {
        default_roots(&root)?
    } else {
        requested.into_iter().map(|path| root.join(path)).collect()
    };
    let mut files = Vec::new();
    for path in roots {
        collect_rust_files(&path, &mut files)?;
    }
    files.sort();
    files.dedup();
    if files.is_empty() {
        return Err("no Rust source files found".to_owned());
    }

    let mut errors = 0usize;
    let mut advisories = 0usize;
    for path in &files {
        let source = fs::read_to_string(path)
            .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
        let diagnostics = analyze_source(&source)
            .map_err(|error| format!("failed to parse {}: {error}", path.display()))?;
        for diagnostic in diagnostics {
            let severity = if diagnostic.rule.is_error() {
                errors += 1;
                "error"
            } else {
                advisories += 1;
                "warning"
            };
            let displayed = path.strip_prefix(&root).unwrap_or(path);
            eprintln!(
                "{}:{}:{}: {severity}[{}]: {}",
                displayed.display(),
                diagnostic.line,
                diagnostic.column,
                diagnostic.rule.code(),
                diagnostic.message,
            );
        }
    }

    eprintln!(
        "ragu-circuit-lint: scanned {} files; {errors} errors, {advisories} advisories",
        files.len()
    );
    Ok(errors == 0 && (!deny_advisories || advisories == 0))
}

fn default_roots(root: &Path) -> Result<Vec<PathBuf>, String> {
    let mut roots = Vec::new();
    let root_source = root.join("src");
    if root_source.is_dir() {
        roots.push(root_source);
    }
    let crates = root.join("crates");
    let entries = fs::read_dir(&crates)
        .map_err(|error| format!("failed to read {}: {error}", crates.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| error.to_string())?;
        let source = entry.path().join("src");
        if source.is_dir() {
            roots.push(source);
        }
    }
    Ok(roots)
}

fn collect_rust_files(path: &Path, output: &mut Vec<PathBuf>) -> Result<(), String> {
    if path.is_file() {
        if path.extension().is_some_and(|extension| extension == "rs") {
            output.push(path.to_owned());
        }
        return Ok(());
    }
    if !path.is_dir() || skip_directory(path) {
        return Ok(());
    }
    let entries = fs::read_dir(path)
        .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| error.to_string())?;
        collect_rust_files(&entry.path(), output)?;
    }
    Ok(())
}

fn skip_directory(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| {
            matches!(
                name,
                ".git" | ".claude" | "benches" | "examples" | "target" | "tests"
            )
        })
}
