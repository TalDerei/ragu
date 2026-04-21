mod codegen;
mod driver;
mod expr;
mod instance;
mod instances;
mod linexp;

use std::{
    fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

use clap::{Parser, Subcommand};
use instance::CircuitInstance;

use crate::instances::{
    point_add_incomplete::PointAddIncompleteInstance,
    point_alloc::{PointAllocInstanceFp, PointAllocInstanceFq},
    point_double::PointDoubleInstance,
    point_negate::PointNegateInstance,
};

struct ExportTarget {
    name: &'static str,
    export: fn(&str, &Path) -> std::io::Result<PathBuf>,
    generated_file: fn(&str, &Path) -> (PathBuf, String),
}

/// Single source of truth for every exported instance: both `export` and `check`
static EXPORT_TARGETS: &[ExportTarget] = &[
    ExportTarget {
        name: "Ragu.Instances.Autogen.Point.AllocFp",
        export: export_instance::<PointAllocInstanceFp>,
        generated_file: generated_file_instance::<PointAllocInstanceFp>,
    },
    ExportTarget {
        name: "Ragu.Instances.Autogen.Point.AllocFq",
        export: export_instance::<PointAllocInstanceFq>,
        generated_file: generated_file_instance::<PointAllocInstanceFq>,
    },
    ExportTarget {
        name: "Ragu.Instances.Autogen.Point.Double",
        export: export_instance::<PointDoubleInstance>,
        generated_file: generated_file_instance::<PointDoubleInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Autogen.Point.AddIncomplete",
        export: export_instance::<PointAddIncompleteInstance>,
        generated_file: generated_file_instance::<PointAddIncompleteInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Autogen.Point.Negate",
        export: export_instance::<PointNegateInstance>,
        generated_file: generated_file_instance::<PointNegateInstance>,
    },
];

impl ExportTarget {
    fn root_import_name(&self) -> String {
        // Drop only the first namespace marker
        self.name.replacen(".Autogen", "", 1)
    }
}

fn default_autogen_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean")
}

#[derive(Parser)]
#[command(name = "lean_extraction")]
#[command(about = "Export generated Lean instance files or check them for exact equality")]
struct Cli {
    #[command(subcommand)]
    command: Command,

    /// Root directory that contains the Lean source tree.
    #[arg(default_value_os_t = default_autogen_root())]
    autogen_root: PathBuf,
}

#[derive(Subcommand, Clone, Copy)]
enum Command {
    /// Write all generated Lean files to disk.
    Export,
    /// Compare the generated Lean files with the files already on disk.
    Check,
}

/// Monomorphized helper used by the static export table below.
fn export_instance<I: CircuitInstance>(
    module_name: &str,
    autogen_root: &Path,
) -> std::io::Result<PathBuf> {
    I::export(module_name, autogen_root)
}

/// Monomorphized helper used by `check` to compute the expected file contents.
fn generated_file_instance<I: CircuitInstance>(
    module_name: &str,
    autogen_root: &Path,
) -> (PathBuf, String) {
    I::generated_file(module_name, autogen_root)
}

fn generated_ragu_root(autogen_root: &Path) -> (PathBuf, String) {
    let path = autogen_root.join("Ragu.lean");
    let mut contents = EXPORT_TARGETS
        .iter()
        .map(|target| format!("import {}", target.root_import_name()))
        .collect::<Vec<_>>()
        .join("\n");
    contents.push('\n');
    (path, contents)
}

fn export_all(autogen_root: &Path) -> std::io::Result<()> {
    for target in EXPORT_TARGETS {
        let path = (target.export)(target.name, autogen_root)?;
        println!("wrote {} to {}", target.name, path.display());
    }

    let (path, contents) = generated_ragu_root(autogen_root);
    fs::write(&path, contents)?;
    println!("wrote Ragu to {}", path.display());

    Ok(())
}

fn check_file(
    name: &str,
    path: PathBuf,
    expected: String,
    mismatches: &mut usize,
) -> std::io::Result<()> {
    match fs::read_to_string(&path) {
        Ok(actual) if actual == expected => {
            println!("ok {name}");
        }
        Ok(_) => {
            eprintln!("mismatch {name} at {}", path.display());
            *mismatches += 1;
        }
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            eprintln!("missing {name} at {}", path.display());
            *mismatches += 1;
        }
        Err(err) => return Err(err),
    }

    Ok(())
}

fn check_all(autogen_root: &Path) -> std::io::Result<bool> {
    let mut mismatches = 0;

    for target in EXPORT_TARGETS {
        let (path, expected) = (target.generated_file)(target.name, autogen_root);
        check_file(target.name, path, expected, &mut mismatches)?;
    }

    let (path, expected) = generated_ragu_root(autogen_root);
    check_file("Ragu", path, expected, &mut mismatches)?;

    if mismatches > 0 {
        eprintln!(
            "\n{mismatches} generated Lean file(s) out of date.\n\
             hint: run `cargo run -p lean_extraction -- export` and commit the result."
        );
    }

    Ok(mismatches == 0)
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let result = match cli.command {
        Command::Export => export_all(&cli.autogen_root).map(|_| ExitCode::SUCCESS),
        Command::Check => check_all(&cli.autogen_root).map(|ok| {
            if ok {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            }
        }),
    };

    match result {
        Ok(code) => code,
        Err(err) => {
            eprintln!("{err}");
            ExitCode::from(1)
        }
    }
}
