use std::{env, path::PathBuf, process::ExitCode};

#[path = "../src/source_lint.rs"]
mod source_lint;

use source_lint::scan_sources;

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
    let mut root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut baseline = PathBuf::from("qa/fuzz/source-lint-baseline.txt");
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
            "--baseline" => {
                let path = arguments
                    .next()
                    .ok_or_else(|| "--baseline requires a path".to_owned())?;
                baseline = PathBuf::from(path);
            }
            "--deny-advisories" => deny_advisories = true,
            "--help" | "-h" => {
                println!(
                    "Usage: circuit_lint [--root PATH] [--baseline PATH] [--deny-advisories] [PATH ...]\n\
                     Parses production Rust source without compiling or executing it.\n\
                     PATH and relative baseline arguments are resolved against --root."
                );
                return Ok(true);
            }
            argument if argument.starts_with('-') => {
                return Err(format!("unknown option `{argument}`"));
            }
            path => requested.push(PathBuf::from(path)),
        }
    }

    let report = scan_sources(&root, &requested, Some(&baseline))?;
    for finding in &report.diagnostics {
        let diagnostic = &finding.diagnostic;
        let severity = if diagnostic.rule.is_error() {
            "error"
        } else {
            "warning"
        };
        eprintln!(
            "{}:{}:{}: {severity}[{}]: {}",
            finding.path.display(),
            diagnostic.line,
            diagnostic.column,
            diagnostic.rule.code(),
            diagnostic.message,
        );
    }

    let errors = report.errors();
    let advisories = report.advisories();
    eprintln!(
        "ragu-circuit-lint: scanned {} files; {errors} errors, {advisories} advisories",
        report.files_scanned,
    );
    Ok(errors == 0 && (!deny_advisories || advisories == 0))
}
