//! Polynomial commitments — mirrors Ragu's polynomial commitment scheme.
//!
//! Real Pedersen crypto on Vesta. Only the proof system is mocked.

use alloc::vec::Vec;
use core::ops::{Add, Mul, Neg};

use ff::Field;
use lazy_static::lazy_static;
use pasta_curves::{Eq, EqAffine, Fp};

const MAX_GENERATORS: usize = 8192;

lazy_static! {
    /// Coefficient generators `g[0..n]`.
    static ref GENERATORS: Vec<EqAffine> = {
        use pasta_curves::{arithmetic::CurveExt as _, group::Curve as _};
        let hasher = Eq::hash_to_curve("mock_ragu:generators");
        (0..MAX_GENERATORS)
            .map(|i| {
                let point = hasher(&i.to_le_bytes());
                point.to_affine()
            })
            .collect()
    };

    /// Blinding generator `h` (unknown discrete log relative to `g`).
    static ref BLINDING_GENERATOR: EqAffine = {
        use pasta_curves::{arithmetic::CurveExt as _, group::Curve as _};
        Eq::hash_to_curve("mock_ragu:blinding")(b"h").to_affine()
    };
}

/// Mirrors `ragu_arithmetic::poly_with_roots`.
#[must_use]
pub fn poly_with_roots(roots: &[Fp]) -> Vec<Fp> {
    let mut coeffs = alloc::vec![Fp::ONE];
    for &root in roots {
        let mut new_coeffs = alloc::vec![Fp::ZERO; coeffs.len() + 1];
        for (i, &c) in coeffs.iter().enumerate() {
            new_coeffs[i + 1] += c;
            new_coeffs[i] += c * root.neg();
        }
        coeffs = new_coeffs;
    }
    coeffs
}

/// Mirrors `ragu_circuits::polynomials::unstructured::Polynomial`.
#[derive(Clone, Debug, Eq)]
pub struct Polynomial(Vec<Fp>);

impl PartialEq for Polynomial {
    fn eq(&self, other: &Self) -> bool {
        self.commit(Fp::ZERO) == other.commit(Fp::ZERO)
    }
}

impl Polynomial {
    #[must_use]
    pub fn from_coeffs(coeffs: &[Fp]) -> Self {
        Self(coeffs.to_vec())
    }

    #[must_use]
    pub fn from_roots(roots: &[Fp]) -> Self {
        Self(poly_with_roots(roots))
    }

    #[must_use]
    pub fn multiply(&self, other: &Self) -> Self {
        let result_len = self.0.len() + other.0.len() - 1;
        let mut result = alloc::vec![Fp::ZERO; result_len];
        for (i, &a) in self.0.iter().enumerate() {
            for (j, &b) in other.0.iter().enumerate() {
                result[i + j] += a * b;
            }
        }
        Self(result)
    }

    #[must_use]
    pub fn coefficients(&self) -> &[Fp] {
        &self.0
    }

    /// Evaluate via Horner's method: `p(x) = c₀ + x(c₁ + x(c₂ + …))`.
    #[must_use]
    pub fn eval(&self, x: Fp) -> Fp {
        self.0.iter().rev().fold(Fp::ZERO, |acc, &c| acc * x + c)
    }

    /// `commit(blind) = ∑ coeffᵢ·gᵢ + blind·h`
    #[must_use]
    pub fn commit(&self, blind: Fp) -> Commitment {
        use pasta_curves::group::{Curve as _, Group as _};

        let generators = &*GENERATORS;
        assert!(
            self.0.len() <= generators.len(),
            "polynomial degree {} exceeds max generators {}",
            self.0.len() - 1,
            generators.len() - 1,
        );

        let mut acc = Eq::identity();
        for (&coeff, &point) in self.0.iter().zip(generators.iter()) {
            acc += Eq::from(point) * coeff;
        }
        acc += Eq::from(*BLINDING_GENERATOR) * blind;

        Commitment(acc.to_affine())
    }
}

impl Default for Polynomial {
    fn default() -> Self {
        Self(alloc::vec![Fp::ONE])
    }
}

/// A Pedersen vector commitment (EC point on Vesta).
#[derive(Clone, Copy, Debug, Eq)]
pub struct Commitment(EqAffine);

impl PartialEq for Commitment {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Commitment {
    /// The identity (zero) point — the commit of the empty polynomial with
    /// zero blinding.
    #[must_use]
    pub fn identity() -> Self {
        use pasta_curves::group::{Curve as _, Group as _};
        Self(Eq::identity().to_affine())
    }

    /// `Σ_{i<len} G_i` — the commit of the all-ones polynomial of length `len`
    /// with zero blinding.
    ///
    /// A public constant for a fixed `len` (it has no secret input). It is the
    /// coefficient-side basis of the homomorphic shift `+ s·Σ G_i`, where the
    /// scalar `s` (e.g. a note commitment) is a private witness; the shift
    /// never makes `s` public.
    #[must_use]
    pub fn generators_sum(len: usize) -> Self {
        use pasta_curves::group::{Curve as _, Group as _};
        let generators = &*GENERATORS;
        assert!(
            len <= generators.len(),
            "length {len} exceeds max generators {}",
            generators.len(),
        );
        let mut acc = Eq::identity();
        for &point in generators.iter().take(len) {
            acc += Eq::from(point);
        }
        Self(acc.to_affine())
    }

    /// The `i`-th coefficient generator `G_i` as a commitment.
    ///
    /// A public constant (no secret input).
    #[must_use]
    pub fn generator(i: usize) -> Self {
        let generators = &*GENERATORS;
        assert!(
            i < generators.len(),
            "generator index {i} exceeds max generators {}",
            generators.len(),
        );
        Self(generators[i])
    }

    /// The blinding generator `H` — the commit of the empty polynomial with
    /// blinding `1`. This is the other half of the homomorphic cm-shift
    /// basis (the H-side).
    #[must_use]
    pub fn blinding_generator() -> Self {
        Self(*BLINDING_GENERATOR)
    }

    #[must_use]
    pub fn inner(&self) -> &EqAffine {
        &self.0
    }
}

impl Add for Commitment {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        use pasta_curves::group::Curve as _;
        Self((Eq::from(self.0) + Eq::from(rhs.0)).to_affine())
    }
}

impl Mul<Fp> for Commitment {
    type Output = Self;

    fn mul(self, rhs: Fp) -> Self {
        use pasta_curves::group::Curve as _;
        Self((Eq::from(self.0) * rhs).to_affine())
    }
}

impl From<Commitment> for [u8; 32] {
    fn from(c: Commitment) -> Self {
        use pasta_curves::group::GroupEncoding as _;
        c.0.to_bytes()
    }
}

impl TryFrom<&[u8; 32]> for Commitment {
    type Error = &'static str;

    fn try_from(bytes: &[u8; 32]) -> core::result::Result<Self, Self::Error> {
        use pasta_curves::group::GroupEncoding as _;
        Option::from(EqAffine::from_bytes(bytes))
            .map(Self)
            .ok_or("invalid curve point")
    }
}
