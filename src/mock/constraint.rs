//! Mock equivalents of ragu's enforce-only field-element gadget utilities.

use ff::Field as _;
use pasta_curves::Fp;

use crate::error::{Error, Result};

/// Enforces `a == 0`. Mirrors `Element::enforce_zero`; returns `Err(Error(err))`
/// where the real constraint would be unsatisfiable (`a` nonzero).
pub fn enforce_zero(a: Fp, err: &'static str) -> Result<()> {
    if bool::from(a.is_zero()) {
        Ok(())
    } else {
        Err(Error(err))
    }
}

/// Enforces `a != 0`, returning `a`. Mirrors `Element::enforce_nonzero`, which
/// fails to synthesize for a zero value.
pub fn enforce_nonzero(a: Fp, err: &'static str) -> Result<Fp> {
    if bool::from(a.is_zero()) {
        Err(Error(err))
    } else {
        Ok(a)
    }
}

/// Multiplicative inverse `a⁻¹`. Mirrors `Element::invert`, which is
/// unsatisfiable for a zero value.
pub fn invert(a: Fp, err: &'static str) -> Result<Fp> {
    Option::from(a.invert()).ok_or(Error(err))
}

/// `a / divisor`. Mirrors `Element::divide`; errors on a zero divisor (real
/// ragu takes a `Nonzero`, pushing this precondition to the type).
pub fn divide(a: Fp, divisor: Fp, err: &'static str) -> Result<Fp> {
    invert(divisor, err).map(|inv| a * inv)
}

/// Enforces `a^{2^k} == 1`. Mirrors `Element::enforce_root_of_unity`.
pub fn enforce_root_of_unity(a: Fp, k: u32, err: &'static str) -> Result<()> {
    let mut value = a;
    for _ in 0..k {
        value = value.square();
    }
    if value == Fp::ONE {
        Ok(())
    } else {
        Err(Error(err))
    }
}

/// Conditionally enforces `a == b`: when `cond` is true, requires `a == b`; when
/// false, imposes nothing. Mirrors `Boolean::conditional_enforce_equal`;
/// returns `Err(Error(err))` where the real constraint would be unsatisfiable
/// (`cond` true and `a != b`).
pub fn conditional_enforce_equal(cond: bool, a: Fp, b: Fp, err: &'static str) -> Result<()> {
    if cond && a != b {
        Err(Error(err))
    } else {
        Ok(())
    }
}
