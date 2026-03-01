//! Smart-pointer wrappers for committed polynomials.
//!
//! [`CommittedPolynomial`] bundles a polynomial, its blinding factor, and a
//! pre-computed commitment into one immutable type.

use ff::Field;
use ragu_arithmetic::{CurveAffine, FixedGenerators};
use rand::CryptoRng;

use crate::polynomials::{Rank, structured, unstructured};

/// A trait implemented by polynomial types that know how to Pedersen-commit
/// themselves, producing a [`CommittedPolynomial`].
pub trait Committable<C: CurveAffine>: Sized {
    /// Commit to this polynomial using the provided blinding factor.
    fn commit_with_blind(
        &self,
        generators: &impl FixedGenerators<C>,
        blind: C::Scalar,
    ) -> CommittedPolynomial<Self, C>;

    /// Commit to this polynomial, sampling a fresh blinding factor from `rng`.
    fn commit(
        &self,
        generators: &impl FixedGenerators<C>,
        rng: &mut impl CryptoRng,
    ) -> CommittedPolynomial<Self, C> {
        let blind = C::Scalar::random(rng);
        self.commit_with_blind(generators, blind)
    }
}

impl<F: Field, R: Rank, C: CurveAffine<ScalarExt = F>> Committable<C>
    for structured::Polynomial<F, R>
{
    fn commit_with_blind(
        &self,
        generators: &impl FixedGenerators<C>,
        blind: C::Scalar,
    ) -> CommittedPolynomial<Self, C> {
        let commitment = structured::RawPolynomial::commit(self, generators, blind);
        CommittedPolynomial {
            poly: self.clone(),
            blind,
            commitment,
        }
    }
}

impl<F: Field, R: Rank, C: CurveAffine<ScalarExt = F>> Committable<C>
    for unstructured::Polynomial<F, R>
{
    fn commit_with_blind(
        &self,
        generators: &impl FixedGenerators<C>,
        blind: C::Scalar,
    ) -> CommittedPolynomial<Self, C> {
        let commitment = unstructured::RawPolynomial::commit(self, generators, blind);
        CommittedPolynomial {
            poly: self.clone(),
            blind,
            commitment,
        }
    }
}

/// A polynomial together with its blinding factor and eagerly-computed
/// commitment.
///
/// The commitment is computed at construction time, so all accessor methods
/// take `&self`.
#[derive(Clone)]
pub struct CommittedPolynomial<P, C: CurveAffine> {
    poly: P,
    blind: C::Scalar,
    commitment: C,
}

impl<P, C: CurveAffine> CommittedPolynomial<P, C> {
    /// Returns the underlying polynomial.
    pub fn poly(&self) -> &P {
        &self.poly
    }

    /// Returns the blinding scalar used at commitment time.
    pub fn blind(&self) -> C::Scalar {
        self.blind
    }

    /// Returns the pre-computed commitment.
    pub fn commitment(&self) -> C {
        self.commitment
    }

    /// Constructs a `CommittedPolynomial` from raw parts **without** verifying
    /// that the commitment is consistent with the polynomial and blind.
    ///
    /// Intended for cases where the commitment is known externally (e.g. from
    /// a proof transcript) or for tests that deliberately craft an inconsistent
    /// triple.
    pub fn new_unchecked(poly: P, blind: C::Scalar, commitment: C) -> Self {
        Self {
            poly,
            blind,
            commitment,
        }
    }
}
