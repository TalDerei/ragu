use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_pasta::{Fp, Fq};

use crate::expr::{Expr, Op};

pub trait FieldExporter: Field {
    fn get_field_definition() -> &'static str;
}

impl FieldExporter for Fp {
    fn get_field_definition() -> &'static str {
        "def p := Core.Primes.p"
    }
}

impl FieldExporter for Fq {
    fn get_field_definition() -> &'static str {
        "def p := Core.Primes.q"
    }
}

fn display_coeff<F: Field + std::fmt::Debug>(c: &Coeff<F>) -> String {
    match c {
        // Type-annotated so that `0`/`1`/`2`-prefixed expressions like `1 + ...`
        // parse without Lean defaulting the literal to `ℕ`.
        Coeff::Zero => "((0 : F p) : Expression (F p))".to_owned(),
        Coeff::One => "((1 : F p) : Expression (F p))".to_owned(),
        Coeff::Two => "((2 : F p) : Expression (F p))".to_owned(),
        // TODO: make this work without the extra coercion to `F p` by making circuit_norm normalize negated expressions consistently
        Coeff::NegativeOne => "((-1 : F p) : Expression (F p))".to_owned(),
        Coeff::Arbitrary(f) => format!("({f:?} : Expression (F p))"),
        Coeff::NegativeArbitrary(f) => format!("((-{f:?} : F p) : Expression (F p))"),
    }
}

fn display_expr<F: Field + std::fmt::Debug>(expr: &Expr<F>) -> String {
    match expr {
        Expr::Var(i) => format!("(var ⟨{i}⟩)"),
        Expr::InputVar(i) => format!("(input_var[{i}])"),
        Expr::Const(c) => display_coeff(c),
        Expr::Add(l, r) => format!("({} + {})", display_expr(l), display_expr(r)),
        Expr::Mul(l, r) => format!("({} * {})", display_expr(l), display_expr(r)),
    }
}

pub fn render_reducible_definition(name: &str, value: impl std::fmt::Display) -> String {
    format!("@[reducible]\ndef {name} := {value}\n")
}

pub fn render_field_definition<F: FieldExporter>() -> String {
    render_reducible_definition(
        "p",
        F::get_field_definition().trim_start_matches("def p := "),
    )
}

pub fn render_input_len(input_len: usize) -> String {
    render_reducible_definition("inputLen", input_len)
}

pub fn render_output_len(output_len: usize) -> String {
    render_reducible_definition("outputLen", output_len)
}

pub fn render_exported_operations<F: Field + std::fmt::Debug>(ops: &[Op<F>]) -> String {
    let mut output = String::from(
        "set_option linter.unusedVariables false in\n\
def exportedOperations (input_var : Vector (Expression (F p)) inputLen) : Operations (F p) := [\n",
    );

    for op in ops {
        match op {
            Op::Witness { count } => {
                output.push_str(&format!(
                    "  Operation.witness {count} (fun _env => default),\n"
                ));
            }
            Op::Assert(expr) => {
                output.push_str(&format!("  Operation.assert ({}),\n", display_expr(expr)));
            }
        }
    }

    output.push(']');
    output.push('\n');
    output
}

pub fn render_exported_output<F: Field + std::fmt::Debug>(wires: &[Expr<F>]) -> String {
    let mut output = String::from(
        "set_option linter.unusedVariables false in\n\
@[reducible]\n\
def exportedOutput (input_var : Vector (Expression (F p)) inputLen) : Vector (Expression (F p)) outputLen := #v[\n",
    );

    for (index, expr) in wires.iter().enumerate() {
        let suffix = if index + 1 == wires.len() { "" } else { "," };
        output.push_str(&format!("  {}{suffix}\n", display_expr(expr)));
    }

    output.push(']');
    output
}

pub fn render_autogen_module<F: FieldExporter + std::fmt::Debug>(
    module_name: &str,
    input_len: usize,
    ops: &[Op<F>],
    wires: &[Expr<F>],
) -> String {
    format!(
        "import Ragu.Core\n\nnamespace {module_name}\nopen Core.Primes\n\n{}\n{}\n{}\n{}\n{}\n\nend {module_name}\n",
        render_field_definition::<F>(),
        render_input_len(input_len),
        render_output_len(wires.len()),
        render_exported_operations(ops),
        render_exported_output(wires),
    )
}
