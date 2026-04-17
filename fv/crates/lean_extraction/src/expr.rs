use ff::Field;
use ragu_arithmetic::Coeff;

/// A symbolic expression over wire indices.
///
/// Mirrors Clean's `Expression F` inductive type:
/// ```lean
/// inductive Expression (F : Type) where
///   | var   : Variable F → Expression F
///   | const : F → Expression F
///   | add   : Expression F → Expression F → Expression F
///   | mul   : Expression F → Expression F → Expression F
/// ```
///
/// Physical wires (allocated by [`ragu_core::drivers::Driver::mul`] and
/// [`ragu_core::drivers::Driver::alloc`] on
/// [`super::driver::ExtractionDriver`]) are represented as [`Expr::Var`].
/// Virtual wires (returned by [`ragu_core::drivers::Driver::add`]) are
/// expression trees built by composing [`Expr::Add`] and [`Expr::Mul`] nodes.
#[derive(Clone)]
pub enum Expr<F: Field> {
    /// A physical wire identified by its allocation index.
    Var(usize),
    /// A physical input wire identified by its allocation index.
    InputVar(usize),
    /// A field element constant (stored symbolically as [`Coeff`]).
    Const(Coeff<F>),
    /// Sum of two sub-expressions.
    Add(Box<Expr<F>>, Box<Expr<F>>),
    /// Product of two sub-expressions.
    Mul(Box<Expr<F>>, Box<Expr<F>>),
}

/// A single operation collected during circuit synthesis.
///
/// Mirrors the flat operations of Clean's `FlatOperation F`:
/// - `Witness` corresponds to `FlatOperation.witness`
/// - `Assert` corresponds to `FlatOperation.assert`
pub enum Op<F: Field> {
    /// Allocation of `count` consecutive wires. Indices are implicit in the
    /// order this op appears in the surrounding sequence.
    Witness { count: usize },
    /// Constraint that the given expression must evaluate to zero.
    Assert(Expr<F>),
}
