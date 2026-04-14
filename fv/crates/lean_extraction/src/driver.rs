use core::marker::PhantomData;

use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::{
    Result,
    drivers::{Driver, DriverTypes},
    maybe::Empty,
};

use crate::expr::{Expr, Op};
use crate::linexp::ExprLc;

/// A Ragu [`Driver`] that symbolically records all generated constraints.
///
/// `ExtractionDriver` runs circuit synthesis without computing any witness
/// values (`MaybeKind = Empty`). Instead it builds a symbolic representation
/// of every constraint:
///
/// - [`Driver::mul`] — allocates three fresh wire indices and records an
///   [`Op::Assert`] for the multiplicative constraint `a · b − c = 0`.
/// - [`Driver::alloc`] — allocates a single fresh wire index and records an
///   [`Op::Witness`].
/// - [`Driver::add`] — builds a virtual wire as a symbolic [`Expr`] tree
///   without allocating a new index or emitting any constraint.
/// - [`Driver::enforce_zero`] — builds a symbolic [`Expr`] and records an
///   [`Op::Assert`].
/// - [`Driver::constant`] — returns an [`Expr::Const`] without any
///   allocation or constraint.
///
/// Wire index 0 is reserved for the constant-1 wire ([`Driver::ONE`]).
/// Fresh allocations begin from index 1.
///
/// After synthesis, the collected [`Op`]s are available via [`ops`].
pub struct ExtractionDriver<F: Field> {
    /// Next wire index to assign on allocation.
    next_wire: usize,
    /// Next input wire index to assign on input allocation.
    next_input_wire: usize,
    /// Ordered sequence of operations recorded during synthesis.
    pub ops: Vec<Op<F>>,
    _phantom: PhantomData<F>,
}

impl<F: Field> ExtractionDriver<F> {
    /// Creates a new extraction driver.
    ///
    /// Wire 0 is pre-reserved as the constant-1 wire; allocations begin at 1.
    pub fn new() -> Self {
        ExtractionDriver {
            next_wire: 1,
            next_input_wire: 0,
            ops: Vec::new(),
            _phantom: PhantomData,
        }
    }

    /// Allocates the next available wire index and advances the counter.
    fn alloc_wire(&mut self) -> usize {
        let idx = self.next_wire;
        self.next_wire += 1;
        idx
    }

    /// Allocates `n` input wires.
    /// NOTE: those are not part of the "main" exported trace.
    pub fn alloc_input_wires(&mut self, n: usize) -> Vec<Expr<F>> {
        let start = self.next_input_wire;
        self.next_input_wire += n;
        (start..start + n).map(Expr::InputVar).collect()
    }
}

impl<F: Field> Default for ExtractionDriver<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: Field> DriverTypes for ExtractionDriver<F> {
    type ImplField = F;
    type ImplWire = Expr<F>;
    type MaybeKind = Empty;
    type LCadd = ExprLc<F>;
    type LCenforce = ExprLc<F>;

    fn gate(
        &mut self,
        _: impl Fn() -> Result<(Coeff<F>, Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> Result<(Expr<F>, Expr<F>, Expr<F>, Expr<F>)> {
        let a = self.alloc_wire();
        let b = self.alloc_wire();
        let c = self.alloc_wire();
        let d = self.alloc_wire();

        self.ops.push(Op::Witness { count: 4 });

        // A * B - C = 0
        let constraint_mul = Expr::Add(
            Box::new(Expr::Mul(Box::new(Expr::Var(a)), Box::new(Expr::Var(b)))),
            Box::new(Expr::Mul(
                Box::new(Expr::Const(Coeff::NegativeOne)),
                Box::new(Expr::Var(c)),
            )),
        );
        self.ops.push(Op::Assert(constraint_mul));

        // C * D = 0
        let constraint_cd = Expr::Mul(Box::new(Expr::Var(c)), Box::new(Expr::Var(d)));
        self.ops.push(Op::Assert(constraint_cd));

        Ok((Expr::Var(a), Expr::Var(b), Expr::Var(c), Expr::Var(d)))
    }
}

impl<'dr, F: Field> Driver<'dr> for ExtractionDriver<F> {
    type F = F;
    type Wire = Expr<F>;

    /// Wire 0 is always the constant-1 wire.
    const ONE: Expr<F> = Expr::Var(0);

    /// Allocates a single wire index and records a [`Op::Witness`] for it.
    ///
    /// Overrides the default implementation (which would call [`mul`] and
    /// waste two extra wire slots) to keep allocations compact.
    fn alloc(&mut self, _: impl Fn() -> Result<Coeff<F>>) -> Result<Expr<F>> {
        let idx = self.alloc_wire();
        self.ops.push(Op::Witness { count: 1 });
        Ok(Expr::Var(idx))
    }

    /// Returns a constant expression without allocating a wire.
    ///
    /// Overrides the default to avoid the indirection through [`add`].
    fn constant(&mut self, coeff: Coeff<F>) -> Expr<F> {
        Expr::Const(coeff)
    }

    /// Allocates three consecutive wire indices for the gate `(a, b, c)` and
    /// records:
    /// 1. [`Op::Witness`] for the three wires.
    /// 2. [`Op::Assert`] for the multiplicative constraint `a · b − c = 0`.
    fn mul(
        &mut self,
        _: impl Fn() -> Result<(Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> Result<(Expr<F>, Expr<F>, Expr<F>)> {
        let a = self.alloc_wire();
        let b = self.alloc_wire();
        let c = self.alloc_wire();

        self.ops.push(Op::Witness { count: 3 });

        // a * b - c = 0
        let constraint = Expr::Add(
            Box::new(Expr::Mul(Box::new(Expr::Var(a)), Box::new(Expr::Var(b)))),
            Box::new(Expr::Mul(
                Box::new(Expr::Const(Coeff::NegativeOne)),
                Box::new(Expr::Var(c)),
            )),
        );
        self.ops.push(Op::Assert(constraint));

        Ok((Expr::Var(a), Expr::Var(b), Expr::Var(c)))
    }

    /// Builds a virtual wire as a symbolic expression.
    ///
    /// No wire index is allocated and no constraint is recorded. The returned
    /// [`Expr`] can be used freely in subsequent [`mul`] and [`enforce_zero`]
    /// calls.
    fn add(&mut self, lc: impl Fn(ExprLc<F>) -> ExprLc<F>) -> Expr<F> {
        lc(ExprLc::default()).into_expr()
    }

    /// Builds the constraint expression and records an [`Op::Assert`].
    fn enforce_zero(&mut self, lc: impl Fn(ExprLc<F>) -> ExprLc<F>) -> Result<()> {
        let expr = lc(ExprLc::default()).into_expr();
        self.ops.push(Op::Assert(expr));
        Ok(())
    }
}
