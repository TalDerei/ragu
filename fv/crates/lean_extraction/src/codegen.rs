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
        Coeff::Zero => "0".to_owned(),
        Coeff::One => "1".to_owned(),
        Coeff::Two => "2".to_owned(),
        Coeff::NegativeOne => format!("({:?} : Expression (F p))", F::ONE.neg()),
        Coeff::Arbitrary(f) => format!("({f:?} : Expression (F p))"),
        Coeff::NegativeArbitrary(f) => format!("({:?} : Expression (F p))", f.neg()),
    }
}

fn display_expr<F: Field + std::fmt::Debug>(expr: &Expr<F>) -> String {
    match expr {
        Expr::Var(i) => {
            if *i == 0 {
                "1".to_owned()
            } else {
                format!("(var {})", i - 1)
            }
        }
        Expr::InputVar(i) => format!("(input_var.get {i})"),
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
def exportedOperations (input_var : Var (ProvableVector field inputLen) (F p)) : Operations (F p) := [\n",
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
    let mut output = format!(
        "set_option linter.unusedVariables false in\n\
@[reducible]\n\
def exportedOutput (input_var : Var (ProvableVector field inputLen) (F p)) : Vector (Expression (F p)) outputLen := #v[\n"
    );

    for (index, expr) in wires.iter().enumerate() {
        let suffix = if index + 1 == wires.len() { "" } else { "," };
        output.push_str(&format!("  {}{suffix}\n", display_expr(expr)));
    }

    output.push(']');
    output
}
