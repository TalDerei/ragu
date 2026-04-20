use core::marker::PhantomData;

use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::{
    Result,
    drivers::{Driver, DriverTypes},
    maybe::Empty,
};

use crate::{
    expr::{Expr, Op},
    linexp::ExprLc,
};

/// A Ragu [`Driver`] that symbolically records all generated constraints.
///
/// `ExtractionDriver` runs circuit synthesis without computing any witness
/// values (`MaybeKind = Empty`). Instead it builds a symbolic representation
/// of every constraint:
///
/// - [`Driver::mul`] / [`DriverTypes::gate`] — allocate three fresh wire
///   indices and record an [`Op::Assert`] for the multiplicative constraint
///   `a * b − c = 0`. The gate does not allocate the auxiliary `D` wire or
///   emit its `C * D = 0` constraint; see [`DriverTypes::Extra`] for the
///   rationale.
/// - [`DriverTypes::assign_extra`] — allocates a single fresh wire and
///   records an [`Op::Witness`], preserving the pre-`gate` `alloc`
///   semantics under the shim.
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
/// After synthesis, the collected [`Op`]s are available via [`Self::ops`].
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
            next_wire: 0,
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

    pub fn input_wire_count(&self) -> usize {
        self.next_input_wire
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

    /// Phantom token: the extractor does not model the $D$ wire of a gate.
    ///
    /// Production drivers allocate a fourth wire $D$ per gate with the
    /// constraint $C \cdot D = 0$, available for reuse via
    /// [`DriverTypes::assign_extra`] when $C$ is known to be zero. The
    /// extractor intentionally under-models this: every
    /// [`DriverTypes::gate`] call emits the old three-wire `mul` shape, and
    /// [`DriverTypes::assign_extra`] allocates a single fresh wire with no
    /// accompanying constraint (matching the old `Driver::alloc`). This keeps
    /// the emitted Lean trace identical to what it was before the D-wire
    /// redesign on main, at the cost of not modeling `C · D = 0` on the
    /// extracted side.
    type Extra = ();

    /// Allocates three consecutive wire indices for a gate `(a, b, c)` and
    /// records:
    /// 1. [`Op::Witness`] for the three wires.
    /// 2. [`Op::Assert`] for the multiplicative constraint `a · b − c = 0`.
    ///
    /// Under the [`DriverTypes::Extra`] shim, no fourth $D$ wire is allocated
    /// and no `C · D = 0` constraint is emitted; the returned
    /// [`DriverTypes::Extra`] token is `()`.
    fn gate(
        &mut self,
        _: impl Fn() -> Result<(Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> Result<(Expr<F>, Expr<F>, Expr<F>, ())> {
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

        Ok((Expr::Var(a), Expr::Var(b), Expr::Var(c), ()))
    }

    /// Allocates a single fresh wire and records an [`Op::Witness`] for it.
    ///
    /// This preserves the old `Driver::alloc` semantics (one wire, no
    /// constraint). The incoming [`DriverTypes::Extra`] token is `()` and
    /// carries no information; production would interpret it as an override
    /// of the $D$ wire's default zero assignment, but the extractor never
    /// allocated a $D$ in the first place.
    fn assign_extra(&mut self, _: (), _: impl Fn() -> Result<Coeff<F>>) -> Result<Expr<F>> {
        let idx = self.alloc_wire();
        self.ops.push(Op::Witness { count: 1 });
        Ok(Expr::Var(idx))
    }
}

impl<'dr, F: Field> Driver<'dr> for ExtractionDriver<F> {
    type F = F;
    type Wire = Expr<F>;

    /// Wire 0 is always the constant-1 wire.
    const ONE: Expr<F> = Expr::Const(Coeff::One);

    /// Returns a constant expression without allocating a wire.
    ///
    /// Overrides the default to avoid the indirection through [`Driver::add`].
    fn constant(&mut self, coeff: Coeff<F>) -> Expr<F> {
        Expr::Const(coeff)
    }

    /// Builds a virtual wire as a symbolic expression.
    ///
    /// No wire index is allocated and no constraint is recorded. The returned
    /// [`Expr`] can be used freely in subsequent [`Driver::mul`] and [`Driver::enforce_zero`]
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
