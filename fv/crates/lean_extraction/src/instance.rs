use core::marker::PhantomData;

use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::convert::WireMap;
use ragu_core::gadgets::Gadget;

use crate::driver::ExtractionDriver;
use crate::expr::{Expr, Op};

/// A [`WireMap`] that collects all physical wires from a gadget by cloning
/// them into a flat [`Vec`].
///
/// Used by [`CircuitInstance`] implementors to manually serialize the output
/// of a circuit into a list of driver wires.
pub struct WireCollector<F: Field> {
    pub wires: Vec<Expr<F>>,
}

impl<F: Field> WireCollector<F> {
    pub fn new() -> Self {
        WireCollector { wires: Vec::new() }
    }

    pub fn collect_from<'dr, G>(gadget: &G) -> ragu_core::Result<Vec<Expr<F>>>
    where
        G: Gadget<'dr, ExtractionDriver<F>>,
        ExtractionDriver<F>: ragu_core::drivers::Driver<'dr, F = F>,
    {
        let mut collector = Self::new();
        gadget.map(&mut collector)?;
        Ok(collector.wires)
    }
}

impl<F: Field> WireMap<F> for WireCollector<F> {
    type Src = ExtractionDriver<F>;
    type Dst = PhantomData<F>;

    fn convert_wire(&mut self, wire: &Expr<F>) -> ragu_core::Result<()> {
        self.wires.push(wire.clone());
        Ok(())
    }
}

/// The inverse of [`WireCollector`]: maps a flat [`Vec`] of [`Expr`] wires
/// back into any gadget, using a *template* gadget to drive the traversal
/// structure.
///
/// # How it works
///
/// [`WireCollector`] serializes a gadget's wires into a flat `Vec<Expr<F>>` by
/// traversing the gadget's wire fields in field-declaration order. `WireDeserializer`
/// reverses this: given the same flat `Vec` it substitutes wires one-by-one
/// (ignoring the template's existing wires) into any gadget that has the same
/// wire count.
///
/// Typically:
/// 2. Obtain a template gadget of the target type with any wires (they are
///    discarded).
/// 3. Call [`WireDeserializer::into_gadget`], which asserts that the wire counts
///    match and produces the target gadget with the deserialized wires.
pub struct WireDeserializer<F: Field> {
    wires: std::vec::IntoIter<Expr<F>>,
}

impl<F: Field> WireDeserializer<F> {
    pub(crate) fn new(wires: Vec<Expr<F>>) -> Self {
        WireDeserializer {
            wires: wires.into_iter(),
        }
    }

    /// Consume this deserializer and produce `template` with its wires replaced
    /// by the wires held in this deserializer.
    ///
    /// # Panics
    ///
    /// Panics if the number of wires remaining in this deserializer does not
    /// equal `template.num_wires()`.
    pub fn into_gadget<'dr, G>(mut self, template: &G) -> ragu_core::Result<G>
    where
        G: Gadget<'dr, ExtractionDriver<F>>,
        ExtractionDriver<F>: ragu_core::drivers::Driver<'dr, F = F>,
    {
        let actual = self.wires.len();
        let expected = template.num_wires()?;
        assert_eq!(
            actual, expected,
            "WireDeserializer: wire count mismatch \
             (source FixedVec has {actual} wires, target gadget expects {expected})"
        );
        template.map(&mut self)
    }
}

impl<F: Field> WireMap<F> for WireDeserializer<F> {
    type Src = ExtractionDriver<F>;
    type Dst = ExtractionDriver<F>;

    /// Ignore `_src` (the template's wire) and return the next wire from the
    /// internal iterator.
    fn convert_wire(&mut self, _src: &Expr<F>) -> ragu_core::Result<Expr<F>> {
        self.wires
            .next()
            .ok_or_else(|| ragu_core::Error::InvalidWitness("WireDeserializer exhausted".into()))
    }
}

fn display_coeff<F: Field + std::fmt::Debug>(c: &Coeff<F>) -> String {
    match c {
        Coeff::Zero => "0".to_owned(),
        Coeff::One => "1".to_owned(),
        Coeff::Two => "2".to_owned(),
        Coeff::NegativeOne => format!("({:?} : Expression CircuitField)", F::ONE.neg()),
        Coeff::Arbitrary(f) => format!("({f:?} : Expression CircuitField)"),
        Coeff::NegativeArbitrary(f) => format!("({:?} : Expression CircuitField)", f.neg()),
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

/// A trait for circuit instances that can be extracted by the driver.
pub trait CircuitInstance {
    type Field: Field + std::fmt::Debug;

    /// Run the circuit on `dr` and return its output.
    /// The output is a vector of expressions corresponding to the
    /// output wires in order. This must include all "interesting" wires for which we
    /// want to prove some properties about.
    /// They have to be physical wires (i.e. `Expr::Var`) since virtual wires cannot be
    /// referenced from outside the circuit.
    fn circuit(dr: &mut ExtractionDriver<Self::Field>)
    -> ragu_core::Result<Vec<Expr<Self::Field>>>;

    /// Run the circuit and print the Lean definitions for operations and output.
    fn export() {
        let mut dr = ExtractionDriver::<Self::Field>::new();
        let wires = Self::circuit(&mut dr).expect("circuit failed");

        println!("set_option linter.unusedVariables false in");
        println!(
            "def exported_operations (input_var : Var Inputs CircuitField) : Operations CircuitField := ["
        );
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
        println!();

        println!("set_option linter.unusedVariables false in");
        print!(
            "def exported_output (input_var : Var Inputs CircuitField) : List (Expression CircuitField) := ["
        );
        for (i, expr) in wires.iter().enumerate() {
            if i > 0 {
                print!(", ");
            }
            print!("{}", display_expr(expr));
        }
        println!("]");
    }
}
