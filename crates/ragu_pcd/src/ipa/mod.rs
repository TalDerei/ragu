//! Inner Product Argument (IPA) for polynomial commitments.
//!
//! Adapted from halo2's `halo2_proofs/src/poly/commitment`. Fiat-Shamir reuses
//! the PCD `Transcript` executed at concrete values via the `Emulator` driver.
//! Host curve commitments are hashed into the circuit-field transcript by
//! reinterpreting each coordinate's little-endian byte representation as a
//! circuit-field element; infinity is rejected, matching halo2's
//! `common_point`.

use alloc::vec::Vec;

use ff::{Field, PrimeField};
use pasta_curves::arithmetic::CurveAffine;
use ragu_arithmetic::{FixedGenerators, PoseidonPermutation, mul as best_multiexp};
use ragu_core::{Error, Result, drivers::Driver};
use ragu_primitives::{Element, GadgetExt};

use crate::internal::transcript::Transcript;

pub mod compress;
mod msm;
mod prover;
mod verifier;

pub use compress::CompressedProof;
pub use msm::MSM;
pub use prover::create_proof;
pub use verifier::verify_proof;

/// Domain separation tag for the IPA sub-protocol.
pub(crate) const IPA_TAG: &[u8] = b"ragu-ipa";

/// These are the public parameters for the polynomial commitment scheme,
/// mirroring halo2's `Params<C>`.
#[derive(Clone, Debug)]
pub struct Params<C: CurveAffine> {
    pub(crate) k: u32,
    pub(crate) n: u64,
    pub(crate) g: Vec<C>,
    pub(crate) w: C,
    pub(crate) u: C,
}

impl<C: CurveAffine> Params<C> {
    /// Bundles an existing [`FixedGenerators`] into halo2-style `Params`.
    pub fn new<G: FixedGenerators<C>>(generators: &G) -> Self {
        let n = generators.g().len() as u64;
        assert!(n.is_power_of_two());
        Params {
            k: n.ilog2(),
            n,
            g: generators.g().to_vec(),
            w: *generators.w(),
            u: *generators.u(),
        }
    }

    /// Commits to a polynomial described by the provided slice of
    /// coefficients. The commitment is blinded by the blinding factor `r`.
    pub fn commit(&self, poly: &[C::Scalar], r: Blind<C::Scalar>) -> C::Curve
    where
        C::Scalar: PrimeField,
    {
        best_multiexp(poly, &self.g) + self.w * r.0
    }
}

/// Wrapper type around a blinding factor, distinguishing it from other
/// scalars at the type level. Mirrors halo2's `Blind<F>`.
#[derive(Copy, Clone, Debug)]
pub struct Blind<F>(pub F);

impl<F: Field> Default for Blind<F> {
    fn default() -> Self {
        Blind(F::ONE)
    }
}

impl<F: Field> core::ops::Add for Blind<F> {
    type Output = Self;

    fn add(self, rhs: Blind<F>) -> Self {
        Blind(self.0 + rhs.0)
    }
}

impl<F: Field> core::ops::Mul for Blind<F> {
    type Output = Self;

    fn mul(self, rhs: Blind<F>) -> Self {
        Blind(self.0 * rhs.0)
    }
}

impl<F: Field> core::ops::AddAssign for Blind<F> {
    fn add_assign(&mut self, rhs: Blind<F>) {
        self.0 += rhs.0;
    }
}

impl<F: Field> core::ops::MulAssign for Blind<F> {
    fn mul_assign(&mut self, rhs: Blind<F>) {
        self.0 *= rhs.0;
    }
}

impl<F: Field> core::ops::AddAssign<F> for Blind<F> {
    fn add_assign(&mut self, rhs: F) {
        self.0 += rhs;
    }
}

impl<F: Field> core::ops::MulAssign<F> for Blind<F> {
    fn mul_assign(&mut self, rhs: F) {
        self.0 *= rhs;
    }
}

/// Log-size IPA proof.
#[derive(Clone, Debug)]
pub struct IpaProof<C: CurveAffine> {
    /// Commitment to blinding polynomial S.
    pub s_commitment: C,
    /// Cross-term commitments $(L_j, R_j)$ per round.
    pub rounds: Vec<(C, C)>,
    /// Final collapsed coefficient.
    pub c: C::ScalarExt,
    /// Synthetic blinding factor.
    pub f: C::ScalarExt,
}

/// Absorb a curve point into the IPA transcript by byte-reinterpreting each
/// coordinate as a transcript-field element. Matches halo2's `common_point`:
/// points at infinity are rejected.
pub(super) fn absorb_point<'dr, C, D, P>(
    dr: &mut D,
    transcript: &mut Transcript<'dr, D, P>,
    point: &C,
) -> Result<()>
where
    C: CurveAffine,
    C::Base: PrimeField,
    D: Driver<'dr>,
    D::F: PrimeField,
    P: PoseidonPermutation<D::F>,
{
    let coords = point.coordinates().into_option().ok_or_else(|| {
        Error::InvalidWitness("cannot write points at infinity to the transcript".into())
    })?;
    let x = field_from_bytes::<D::F>(coords.x().to_repr().as_ref());
    let y = field_from_bytes::<D::F>(coords.y().to_repr().as_ref());
    Element::constant(dr, x).write(dr, transcript)?;
    Element::constant(dr, y).write(dr, transcript)?;
    Ok(())
}

/// Reinterpret the little-endian bytes of a scalar from one prime field as an
/// element of another. Host curve commitments have coordinates in
/// `C::ScalarField` but Ragu's transcript sponges over `C::CircuitField`, so
/// each coordinate is byte-reinterpreted before being absorbed.
pub(super) fn field_from_bytes<F: PrimeField>(bytes: &[u8]) -> F {
    let mut repr = F::Repr::default();
    let len = core::cmp::min(bytes.len(), repr.as_ref().len());
    repr.as_mut()[..len].copy_from_slice(&bytes[..len]);
    F::from_repr_vartime(repr).unwrap_or_else(|| {
        bytes
            .iter()
            .take(32)
            .enumerate()
            .fold(F::ZERO, |acc, (i, &b)| {
                acc + F::from(b as u64) * F::from(256u64).pow([i as u64])
            })
    })
}
