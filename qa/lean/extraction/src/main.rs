mod driver;
mod expr;
mod fingerprint;
mod instance;
mod instances;
mod linexp;
mod sha256;
mod wire_remap;

use std::{
    fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

use clap::{Parser, Subcommand};
use ff::PrimeField;
use instance::CircuitInstance;
use ragu_arithmetic::PoseidonPermutation;
use ragu_pasta::{Fp, Fq, PoseidonFp, PoseidonFq};

use crate::instances::{
    boolean_alloc::BooleanAllocInstance,
    boolean_and::BooleanAndInstance,
    boolean_conditional_enforce_equal::BooleanConditionalEnforceEqualInstance,
    boolean_conditional_select::BooleanConditionalSelectInstance,
    core_mul::CoreMulInstance,
    element_alloc::ElementAllocInstance,
    element_alloc_square::ElementAllocSquareInstance,
    element_div_nonzero::ElementDivNonzeroInstance,
    element_enforce_nonzero::ElementEnforceNonzeroInstance,
    element_enforce_root_of_unity::{
        ElementEnforceRootOfUnityInstanceK2, ElementEnforceRootOfUnityInstanceK5,
    },
    element_enforce_zero::ElementEnforceZeroInstance,
    element_fold::{ElementFoldInstanceN3, ElementFoldInstanceN7, ElementFoldInstanceN19},
    element_invert::ElementInvertInstance,
    element_invert_with::ElementInvertWithInstance,
    element_is_equal::ElementIsEqualInstance,
    element_is_zero::ElementIsZeroInstance,
    element_mul::ElementMulInstance,
    element_square::ElementSquareInstance,
    endoscalar_alloc::EndoscalarAllocInstance,
    endoscalar_extract::EndoscalarExtractInstance,
    endoscalar_group_scale::EndoscalarGroupScaleInstance,
    endoscalar_lift::EndoscalarLiftInstance,
    horner::{HornerInstanceN3, HornerInstanceN7, HornerInstanceN19, HornerKyInstanceN3},
    nonzero_bank_scope::NonzeroBankScopeInstanceK2,
    point_add_incomplete::PointAddIncompleteInstance,
    point_alloc::{PointAllocInstanceFp, PointAllocInstanceFq},
    point_conditional_endo::PointConditionalEndoInstance,
    point_conditional_negate::PointConditionalNegateInstance,
    point_double::PointDoubleInstance,
    point_double_and_add_incomplete::PointDoubleAndAddIncompleteInstance,
    poseidon_sponge::{PoseidonHash1InstanceFp, PoseidonHash1InstanceFq, PoseidonHash4InstanceFp},
};

struct ExportTarget {
    /// Lean module name of the (handwritten) formal instance.
    name: &'static str,
    /// Computes the canonical digest of the instance's extracted trace.
    fingerprint: fn() -> String,
}

/// Single source of truth for every exported instance: `export`, `check` and
/// `fingerprint` all enumerate this table.
static EXPORT_TARGETS: &[ExportTarget] = &[
    ExportTarget {
        name: "Ragu.Instances.Point.AllocFp",
        fingerprint: fingerprint_instance::<PointAllocInstanceFp>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.AllocFq",
        fingerprint: fingerprint_instance::<PointAllocInstanceFq>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.Double",
        fingerprint: fingerprint_instance::<PointDoubleInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.DoubleAndAddIncomplete",
        fingerprint: fingerprint_instance::<PointDoubleAndAddIncompleteInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.AddIncomplete",
        fingerprint: fingerprint_instance::<PointAddIncompleteInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.ConditionalEndo",
        fingerprint: fingerprint_instance::<PointConditionalEndoInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Point.ConditionalNegate",
        fingerprint: fingerprint_instance::<PointConditionalNegateInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.Mul",
        fingerprint: fingerprint_instance::<ElementMulInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.Square",
        fingerprint: fingerprint_instance::<ElementSquareInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.Alloc",
        fingerprint: fingerprint_instance::<ElementAllocInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.AllocSquare",
        fingerprint: fingerprint_instance::<ElementAllocSquareInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.DivNonzero",
        fingerprint: fingerprint_instance::<ElementDivNonzeroInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.FoldN3",
        fingerprint: fingerprint_instance::<ElementFoldInstanceN3>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.FoldN7",
        fingerprint: fingerprint_instance::<ElementFoldInstanceN7>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.FoldN19",
        fingerprint: fingerprint_instance::<ElementFoldInstanceN19>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.EnforceRootOfUnityK2",
        fingerprint: fingerprint_instance::<ElementEnforceRootOfUnityInstanceK2>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.EnforceRootOfUnityK5",
        fingerprint: fingerprint_instance::<ElementEnforceRootOfUnityInstanceK5>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.EnforceZero",
        fingerprint: fingerprint_instance::<ElementEnforceZeroInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.Invert",
        fingerprint: fingerprint_instance::<ElementInvertInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.InvertWith",
        fingerprint: fingerprint_instance::<ElementInvertWithInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.EnforceNonzero",
        fingerprint: fingerprint_instance::<ElementEnforceNonzeroInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.NonzeroBank.ScopeK2",
        fingerprint: fingerprint_instance::<NonzeroBankScopeInstanceK2>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.IsEqual",
        fingerprint: fingerprint_instance::<ElementIsEqualInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Element.IsZero",
        fingerprint: fingerprint_instance::<ElementIsZeroInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Core.Mul",
        fingerprint: fingerprint_instance::<CoreMulInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Boolean.Alloc",
        fingerprint: fingerprint_instance::<BooleanAllocInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Boolean.And",
        fingerprint: fingerprint_instance::<BooleanAndInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Boolean.ConditionalSelect",
        fingerprint: fingerprint_instance::<BooleanConditionalSelectInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Boolean.ConditionalEnforceEqual",
        fingerprint: fingerprint_instance::<BooleanConditionalEnforceEqualInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Endoscalar.Alloc",
        fingerprint: fingerprint_instance::<EndoscalarAllocInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Endoscalar.Extract",
        fingerprint: fingerprint_instance::<EndoscalarExtractInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Endoscalar.GroupScale",
        fingerprint: fingerprint_instance::<EndoscalarGroupScaleInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Endoscalar.Lift",
        fingerprint: fingerprint_instance::<EndoscalarLiftInstance>,
    },
    ExportTarget {
        name: "Ragu.Instances.Horner.N3",
        fingerprint: fingerprint_instance::<HornerInstanceN3>,
    },
    ExportTarget {
        name: "Ragu.Instances.Horner.N7",
        fingerprint: fingerprint_instance::<HornerInstanceN7>,
    },
    ExportTarget {
        name: "Ragu.Instances.Horner.N19",
        fingerprint: fingerprint_instance::<HornerInstanceN19>,
    },
    ExportTarget {
        name: "Ragu.Instances.Horner.KyN3",
        fingerprint: fingerprint_instance::<HornerKyInstanceN3>,
    },
    ExportTarget {
        name: "Ragu.Instances.Poseidon.Hash1Fp",
        fingerprint: fingerprint_instance::<PoseidonHash1InstanceFp>,
    },
    ExportTarget {
        name: "Ragu.Instances.Poseidon.Hash4Fp",
        fingerprint: fingerprint_instance::<PoseidonHash4InstanceFp>,
    },
    ExportTarget {
        name: "Ragu.Instances.Poseidon.Hash1Fq",
        fingerprint: fingerprint_instance::<PoseidonHash1InstanceFq>,
    },
];

/// The Lean source tree (`qa/lean/`) is the parent directory of this crate.
fn default_autogen_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..")
}

#[derive(Parser)]
#[command(name = "lean_extraction")]
#[command(about = "Export/check generated Lean files and fingerprint extracted circuit traces")]
struct Cli {
    #[command(subcommand)]
    command: Command,

    /// Root directory that contains the Lean source tree.
    #[arg(default_value_os_t = default_autogen_root())]
    autogen_root: PathBuf,
}

#[derive(Subcommand, Clone, Copy)]
enum Command {
    /// Write the generated Lean files (the instance import root and the
    /// fingerprint instance list) to disk.
    Export,
    /// Compare the generated Lean files with the files already on disk.
    Check,
    /// Print the canonical fingerprint digest of every exported instance.
    ///
    /// CI compares this output against the same digests computed in Lean from
    /// the Clean reimplementations.
    Fingerprint,
}

/// Monomorphized helper used by the static export target table.
fn fingerprint_instance<I: CircuitInstance>() -> String {
    I::fingerprint()
}

fn generated_instances_root(autogen_root: &Path) -> (PathBuf, String) {
    let path = autogen_root.join("Ragu/Instances.lean");
    let mut contents = EXPORT_TARGETS
        .iter()
        .map(|target| format!("import {}", target.name))
        .collect::<Vec<_>>()
        .join("\n");
    contents.push('\n');
    (path, contents)
}

/// Generated list pairing every formal instance with its module name, used by
/// the `fingerprints` executable on the Lean side.
fn generated_fingerprint_instances(autogen_root: &Path) -> (PathBuf, String) {
    let path = autogen_root.join("Ragu/Fingerprint/Instances.lean");
    let entries = EXPORT_TARGETS
        .iter()
        .map(|target| target.name)
        .map(|name| format!("  (\"{name}\", {name}.formal_instance)"))
        .collect::<Vec<_>>()
        .join(",\n");
    let contents = format!(
        "import Ragu.Fingerprint\nimport Ragu.Instances\n\nnamespace Ragu.Fingerprint\n\n\
         /-- Every exported circuit instance, paired with its Lean module name.\n\n\
         Autogenerated by `lean_extraction`; do not edit. Used by the `fingerprints`\n\
         executable, whose output CI compares against\n\
         `cargo run -p lean_extraction -- fingerprint`. -/\n\
         def instances : List (String × Ragu.Core.Statements.FormalInstance) := [\n{entries}\n]\n\n\
         end Ragu.Fingerprint\n"
    );
    (path, contents)
}

/// Big-endian hex literal of a field element, as Lean reads numerals.
fn hex_field_element<F: PrimeField>(x: &F) -> String {
    let repr = x.to_repr();
    let mut hex = String::from("0x");
    // `to_repr` is little-endian for the Pasta fields; Lean numerals are
    // big-endian.
    for byte in repr.as_ref().iter().rev() {
        hex.push_str(&format!("{byte:02x}"));
    }
    hex
}

/// Renders `rows` as a nested `#v[#v[…], …]` literal of `F p` elements.
fn lean_matrix_literal<'a, F: PrimeField + 'a>(rows: impl Iterator<Item = &'a [F]>) -> String {
    let rows = rows
        .map(|row| {
            let cells = row
                .iter()
                .map(hex_field_element)
                .collect::<Vec<_>>()
                .join(",\n      ");
            format!("  #v[\n      {cells}]")
        })
        .collect::<Vec<_>>()
        .join(",\n");
    format!("#v[\n{rows}]")
}

/// Generated Poseidon parameter module for one field: the concrete round
/// constants and MDS matrix the Lean reimplementation is instantiated with.
///
/// The fingerprint check would catch a drifted constant anyway (every
/// round constant and MDS entry is a coefficient of some assert), but
/// generating the file makes the provenance explicit and lets `check` report
/// the drift by name.
fn generated_poseidon_params<F: PrimeField, P: PoseidonPermutation<F>>(
    autogen_root: &Path,
    params: &P,
    suffix: &str,
    prime: &str,
    rust_module: &str,
) -> (PathBuf, String) {
    let path = autogen_root.join(format!("Ragu/Circuits/Poseidon/Params{suffix}.lean"));
    let width = P::T;
    let rounds = P::FULL_ROUNDS + P::PARTIAL_ROUNDS;
    let round_constants = lean_matrix_literal(params.round_constants());
    let mds = lean_matrix_literal(params.mds_matrix());
    let contents = format!(
        "import Ragu.Core\n\n\
         /-!\n\
         Poseidon parameters of `{rust_module}` (`crates/ragu_pasta/src/`): state width\n\
         `{width}`, rate `{rate}`, `x^{alpha}` S-box, `{full}` full and `{partial}` partial rounds.\n\n\
         Autogenerated by `lean_extraction`; do not edit. `cargo run -p lean_extraction\n\
         -- check` fails CI if this file drifts from the Rust constants.\n\
         -/\n\n\
         namespace Ragu.Circuits.Poseidon.Params{suffix}\n\n\
         @[reducible]\n\
         def p := Core.Primes.{prime}\n\n\
         def width : ℕ := {width}\n\
         def rate : ℕ := {rate}\n\
         def alpha : ℕ := {alpha}\n\
         def fullRounds : ℕ := {full}\n\
         def partialRounds : ℕ := {partial}\n\n\
         /-- One vector of `width` round constants per round, in round order. -/\n\
         def roundConstants : Vector (Vector (F p) {width}) {rounds} := {round_constants}\n\n\
         /-- The MDS matrix, row by row. -/\n\
         def mds : Vector (Vector (F p) {width}) {width} := {mds}\n\n\
         end Ragu.Circuits.Poseidon.Params{suffix}\n",
        rate = P::RATE,
        alpha = P::ALPHA,
        full = P::FULL_ROUNDS,
        partial = P::PARTIAL_ROUNDS,
    );
    (path, contents)
}

/// Every generated Lean file, paired with its display name.
fn generated_files(autogen_root: &Path) -> Vec<(&'static str, PathBuf, String)> {
    let (instances_path, instances) = generated_instances_root(autogen_root);
    let (fingerprint_path, fingerprint) = generated_fingerprint_instances(autogen_root);
    let (params_fp_path, params_fp) =
        generated_poseidon_params::<Fp, _>(autogen_root, &PoseidonFp, "Fp", "p", "PoseidonFp");
    let (params_fq_path, params_fq) =
        generated_poseidon_params::<Fq, _>(autogen_root, &PoseidonFq, "Fq", "q", "PoseidonFq");
    vec![
        ("Ragu.Instances", instances_path, instances),
        ("Ragu.Fingerprint.Instances", fingerprint_path, fingerprint),
        ("Ragu.Circuits.Poseidon.ParamsFp", params_fp_path, params_fp),
        ("Ragu.Circuits.Poseidon.ParamsFq", params_fq_path, params_fq),
    ]
}

fn export_all(autogen_root: &Path) -> std::io::Result<()> {
    for (name, path, contents) in generated_files(autogen_root) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&path, contents)?;
        println!("wrote {name} to {}", path.display());
    }

    Ok(())
}

/// Print `<module name> <digest>` for every exported instance.
fn fingerprint_all() {
    for target in EXPORT_TARGETS {
        println!("{} {}", target.name, (target.fingerprint)());
    }
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

    for (name, path, expected) in generated_files(autogen_root) {
        check_file(name, path, expected, &mut mismatches)?;
    }

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
        Command::Fingerprint => {
            fingerprint_all();
            Ok(ExitCode::SUCCESS)
        }
    };

    match result {
        Ok(code) => code,
        Err(err) => {
            eprintln!("{err}");
            ExitCode::from(1)
        }
    }
}
