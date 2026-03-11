mod driver;
mod expr;
mod linexp;

use core::marker::PhantomData;

use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::Point;

use ragu_core::convert::WireMap;
use ragu_core::drivers::Driver;
use ragu_core::gadgets::Gadget;

use driver::ExtractionDriver;
use expr::{Expr, Op};

fn display_coeff<F: Field + std::fmt::Debug>(c: &Coeff<F>) -> String {
    match c {
        Coeff::Zero => "0".to_owned(),
        Coeff::One => "1".to_owned(),
        Coeff::Two => "2".to_owned(),
        Coeff::NegativeOne => format!("{:?}", F::ONE.neg()),
        Coeff::Arbitrary(f) => format!("{f:?}"),
        Coeff::NegativeArbitrary(f) => format!("-({f:?})"),
    }
}

fn display_expr<F: Field + std::fmt::Debug>(expr: &Expr<F>) -> String {
    match expr {
        Expr::Var(i) => {
            if *i == 0 {
                // var at 0 is the ONE wire
                "1".to_owned()
            } else {
                // everything else is a proper variable in the circuit,
                // we re-index to start at 0
                let var_index = i - 1;
                format!("(var {var_index})")
            }
        }
        Expr::Const(c) => display_coeff(c),
        Expr::Add(l, r) => format!("({} + {})", display_expr(l), display_expr(r)),
        Expr::Mul(l, r) => format!("({} * {})", display_expr(l), display_expr(r)),
    }
}

/// A [`WireMap`] that collects the wire indices from all [`Expr::Var`] wires
/// in a gadget. Analogous to the `WireCounter` inside [`Gadget::num_wires`],
/// but records the actual index of each physical wire instead of just counting.
struct WireIndexCollector<F: Field> {
    indices: Vec<usize>,
    _marker: PhantomData<F>,
}

impl<F: Field> WireMap<F> for WireIndexCollector<F> {
    type Src = ExtractionDriver<F>;
    type Dst = PhantomData<F>;

    fn convert_wire(&mut self, wire: &Expr<F>) -> ragu_core::Result<()> {
        match wire {
            Expr::Var(idx) => {
                self.indices.push(*idx);
                Ok(())
            }
            _ => panic!("output wire is not a physical wire (Expr::Var)"),
        }
    }
}

fn main() {
    let mut dr = ExtractionDriver::<Fp>::new();

    // MaybeKind = Empty: the closure is never called.
    let assignment: ragu_core::maybe::Empty = ExtractionDriver::<Fp>::just(|| Fp::ZERO);
    let output = Point::<_, EpAffine>::alloc(&mut dr, assignment).expect("Point::alloc failed");

    println!("Point::alloc: {} operations", dr.ops.len());
    println!("def operations : Operations CircuitField := [");
    for op in &dr.ops {
        match op {
            Op::Witness { count } => {
                println!("  Operation.witness {count} (fun _env => default),");
            }
            Op::Assert(expr) => {
                println!("  Operation.assert ({}),", display_expr(expr));
            }
        }
    }
    println!("]");

    let mut collector = WireIndexCollector::<Fp> {
        indices: Vec::new(),
        _marker: PhantomData,
    };
    output
        .map(&mut collector)
        .expect("wire index collection failed");
    // Re-index: wire 0 is the ONE wire, allocations start at 1, so var N = wire N+1.
    let lean_indices: Vec<usize> = collector.indices.iter().map(|i| i - 1).collect();
    print!("def output : List Nat := [");
    for (i, idx) in lean_indices.iter().enumerate() {
        if i > 0 {
            print!(", ");
        }
        print!("{idx}");
    }
    println!("]");
}
