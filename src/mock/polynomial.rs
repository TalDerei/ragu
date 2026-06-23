//! Polynomial commitments — mirrors Ragu's polynomial commitment scheme.
//!
//! Real Pedersen crypto on Vesta, against the real Ragu generators. A commitment
//! is just the curve point (`Eq`) that `ragu_arithmetic::mul` returns — exactly
//! what real ragu's `Polynomial::commit` produces (`C::Curve`), with no
//! mock-specific wrapper — and the generators are the real
//! [`ragu_pasta::VestaGenerators`]. Only the proof system is mocked.

use alloc::vec::Vec;

use ragu_arithmetic::ff::Field as _;
use ragu_arithmetic::{Cycle as _, FixedGenerators as _};
use ragu_circuits::polynomials::{ProductionRank, Rank};
use ragu_pasta::Pasta;
use ragu_pasta::{Eq, Fp};

/// Mirrors `ragu_circuits::polynomials::unstructured::Polynomial`.
#[derive(Clone, Debug)]
pub struct Polynomial(Vec<Fp>);

impl Polynomial {
    pub const MAX: usize = 1 << <ProductionRank as Rank>::RANK;

    #[must_use]
    pub fn from_coeffs(coeffs: &[Fp]) -> Self {
        Self(coeffs.to_vec())
    }

    #[must_use]
    pub fn from_roots(roots: &[Fp]) -> Self {
        Self::from_coeffs(&ragu_arithmetic::poly_with_roots(roots))
    }

    #[must_use]
    pub fn multiply(&self, other: &Self) -> Self {
        let mut result = Vec::new();
        ragu_arithmetic::poly_mul(&self.0, &other.0, &mut result);
        Self::from_coeffs(&result)
    }

    #[must_use]
    pub fn coefficients(&self) -> &[Fp] {
        &self.0
    }

    /// Evaluate at `x` via the real `ragu_arithmetic::eval` (Horner's method).
    #[must_use]
    pub fn eval(&self, x: Fp) -> Fp {
        ragu_arithmetic::eval(&self.0, x)
    }

    /// `commit() = ∑ coeffᵢ·gᵢ` -- the unblinded coefficient commitment, the
    /// Vesta point `ragu_arithmetic::mul` returns.
    #[must_use]
    pub fn commit(&self) -> Eq {
        let coeffs = self.0.clone();
        let g = Pasta::host_generators(Pasta::baked()).g();
        assert!(
            coeffs.len() <= g.len(),
            "polynomial degree {} exceeds max generators {}",
            coeffs.len() - 1,
            g.len() - 1
        );
        ragu_arithmetic::mul(coeffs.iter(), g[..coeffs.len()].iter())
    }
}

impl Default for Polynomial {
    fn default() -> Self {
        Self::from_coeffs(&[Fp::ONE])
    }
}
