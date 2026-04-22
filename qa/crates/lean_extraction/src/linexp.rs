use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::drivers::LinearExpression;

use crate::expr::Expr;

/// Linear expression accumulator for [`super::driver::ExtractionDriver`].
///
/// Tracks an accumulated symbolic [`Expr`] and a current gain factor. The gain
/// is folded into each new term as it is added, exactly matching the semantics
/// of [`LinearExpression::gain`].
///
/// Used as both `LCadd` (for virtual wires from [`ragu_core::drivers::Driver::add`]) and
/// `LCenforce` (for constraints from [`ragu_core::drivers::Driver::enforce_zero`]).
pub struct ExprLc<F: Field> {
    /// Accumulated expression; `None` represents the additive identity (zero).
    expr: Option<Expr<F>>,
    /// Current gain factor applied to every subsequent [`LinearExpression::add_term`] call.
    gain: Coeff<F>,
}

impl<F: Field> Default for ExprLc<F> {
    fn default() -> Self {
        Self {
            expr: None,
            gain: Coeff::One,
        }
    }
}

impl<F: Field> ExprLc<F> {
    /// Consume this accumulator and return the built expression.
    ///
    /// Returns [`Expr::Const`]`(`[`Coeff::Zero`]`)` if no terms were added.
    pub fn into_expr(self) -> Expr<F> {
        self.expr.unwrap_or(Expr::Const(Coeff::Zero))
    }
}

impl<F: Field> LinearExpression<Expr<F>, F> for ExprLc<F> {
    fn add_term(mut self, wire: &Expr<F>, coeff: Coeff<F>) -> Self {
        let effective = coeff * self.gain;

        // Skip zero-coefficient terms.
        if effective.is_zero() {
            return self;
        }

        // Build the scaled term: for coefficient One we omit the explicit
        // multiplication node to keep the expression compact.
        let term = match effective {
            Coeff::One => wire.clone(),
            other => Expr::Mul(Box::new(Expr::Const(other)), Box::new(wire.clone())),
        };

        self.expr = Some(match self.expr {
            None => term,
            Some(acc) => Expr::Add(Box::new(acc), Box::new(term)),
        });

        self
    }

    fn gain(mut self, coeff: Coeff<F>) -> Self {
        self.gain = self.gain * coeff;
        self
    }
}
