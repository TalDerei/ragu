//! Proof component structs. Each component pairs a `Native*` struct
//! (host-curve data) with a shared [`Bridge`] struct (cross-curve data
//! that bridges to the inner verifier).

use ff::Field;
use ragu_arithmetic::Cycle;
use ragu_circuits::{
    polynomials::{Rank, structured, unstructured},
    registry::CircuitIndex,
};
use ragu_core::{
    drivers::Driver,
    maybe::{Always, Maybe},
};
use ragu_primitives::Element;
use rand::CryptoRng;

use alloc::vec::Vec;

/// A grouped `(rx, blind, commitment)` triple for a native-field rx polynomial.
///
/// The `commitment` is the Pedersen commitment to `rx` under blinding scalar
/// `blind`.
#[derive(Clone)]
pub struct RxTriple<C: Cycle, R: Rank> {
    /// The rx polynomial.
    pub(crate) rx: structured::Polynomial<C::CircuitField, R>,

    /// The Pedersen blinding scalar for `rx`.
    pub(crate) blind: C::CircuitField,

    /// The Pedersen commitment to `rx` under `blind`.
    pub(crate) commitment: C::HostCurve,
}

#[derive(Clone)]
pub(crate) struct Application<C: Cycle, R: Rank> {
    pub(crate) circuit_id: CircuitIndex,
    pub(crate) left_header: Vec<C::CircuitField>,
    pub(crate) right_header: Vec<C::CircuitField>,
    pub(crate) rx_triple: RxTriple<C, R>,
}

#[derive(Clone)]
pub(crate) struct Bridge<C: Cycle, R: Rank> {
    pub(crate) rx: structured::Polynomial<C::ScalarField, R>,
    pub(crate) blind: C::ScalarField,
    pub(crate) commitment: C::NestedCurve,
}

impl<C: Cycle, R: Rank> Bridge<C, R> {
    pub(crate) fn commit(
        params: &C::Params,
        rng: &mut impl CryptoRng,
        rx: structured::Polynomial<C::ScalarField, R>,
    ) -> Self {
        let blind = C::ScalarField::random(&mut *rng);
        let commitment = rx.commit_to_affine(C::nested_generators(params), blind);
        Bridge {
            rx,
            blind,
            commitment,
        }
    }
}

#[derive(Clone)]
pub(crate) struct Preamble<C: Cycle, R: Rank> {
    pub(crate) native: RxTriple<C, R>,
    pub(crate) bridge: Bridge<C, R>,
}

#[derive(Clone)]
pub(crate) struct NativeSPrime<C: Cycle, R: Rank> {
    pub(crate) registry_wx0_poly: unstructured::Polynomial<C::CircuitField, R>,
    pub(crate) registry_wx0_blind: C::CircuitField,
    pub(crate) registry_wx0_commitment: C::HostCurve,
    pub(crate) registry_wx1_poly: unstructured::Polynomial<C::CircuitField, R>,
    pub(crate) registry_wx1_blind: C::CircuitField,
    pub(crate) registry_wx1_commitment: C::HostCurve,
}

#[derive(Clone)]
pub(crate) struct SPrime<C: Cycle, R: Rank> {
    pub(crate) native: NativeSPrime<C, R>,
    pub(crate) bridge: Bridge<C, R>,
}

#[derive(Clone)]
pub(crate) struct NativeInnerError<C: Cycle, R: Rank> {
    pub(crate) registry_wy_poly: structured::Polynomial<C::CircuitField, R>,
    pub(crate) registry_wy_blind: C::CircuitField,
    pub(crate) registry_wy_commitment: C::HostCurve,
    pub(crate) rx_triple: RxTriple<C, R>,
}

#[derive(Clone)]
pub(crate) struct InnerError<C: Cycle, R: Rank> {
    pub(crate) native: NativeInnerError<C, R>,
    pub(crate) bridge: Bridge<C, R>,
}

#[derive(Clone)]
pub(crate) struct OuterError<C: Cycle, R: Rank> {
    pub(crate) native: RxTriple<C, R>,
    pub(crate) bridge: Bridge<C, R>,
}

#[derive(Clone)]
pub(crate) struct NativeAB<C: Cycle, R: Rank> {
    pub(crate) a_poly: structured::Polynomial<C::CircuitField, R>,
    pub(crate) a_blind: C::CircuitField,
    pub(crate) a_commitment: C::HostCurve,
    pub(crate) b_poly: structured::Polynomial<C::CircuitField, R>,
    pub(crate) b_blind: C::CircuitField,
    pub(crate) b_commitment: C::HostCurve,
    pub(crate) c: C::CircuitField,
}

#[derive(Clone)]
pub(crate) struct AB<C: Cycle, R: Rank> {
    pub(crate) native: NativeAB<C, R>,
    pub(crate) bridge: Bridge<C, R>,
}

#[derive(Clone)]
pub(crate) struct NativeQuery<C: Cycle, R: Rank> {
    pub(crate) registry_xy_poly: unstructured::Polynomial<C::CircuitField, R>,
    pub(crate) registry_xy_blind: C::CircuitField,
    pub(crate) registry_xy_commitment: C::HostCurve,
    pub(crate) rx_triple: RxTriple<C, R>,
}

#[derive(Clone)]
pub(crate) struct Query<C: Cycle, R: Rank> {
    pub(crate) native: NativeQuery<C, R>,
    pub(crate) bridge: Bridge<C, R>,
}

#[derive(Clone)]
pub(crate) struct NativeF<C: Cycle, R: Rank> {
    pub(crate) poly: unstructured::Polynomial<C::CircuitField, R>,
    pub(crate) blind: C::CircuitField,
    pub(crate) commitment: C::HostCurve,
}

#[derive(Clone)]
pub(crate) struct F<C: Cycle, R: Rank> {
    pub(crate) native: NativeF<C, R>,
    pub(crate) bridge: Bridge<C, R>,
}

#[derive(Clone)]
pub(crate) struct Eval<C: Cycle, R: Rank> {
    pub(crate) native: RxTriple<C, R>,
    pub(crate) bridge: Bridge<C, R>,
}

#[derive(Clone)]
pub(crate) struct NativeP<C: Cycle, R: Rank> {
    pub(crate) poly: unstructured::Polynomial<C::CircuitField, R>,
    pub(crate) blind: C::CircuitField,
    pub(crate) commitment: C::HostCurve,
    pub(crate) v: C::CircuitField,
}

#[derive(Clone)]
pub(crate) struct NestedP<C: Cycle, R: Rank> {
    pub(crate) step_rxs: Vec<structured::Polynomial<C::ScalarField, R>>,
    pub(crate) endoscalar_rx: structured::Polynomial<C::ScalarField, R>,
    pub(crate) points_rx: structured::Polynomial<C::ScalarField, R>,
}

#[derive(Clone)]
pub(crate) struct P<C: Cycle, R: Rank> {
    pub(crate) native: NativeP<C, R>,
    pub(crate) nested: NestedP<C, R>,
}

#[derive(Clone)]
pub(crate) struct Challenges<C: Cycle> {
    pub(crate) w: C::CircuitField,
    pub(crate) y: C::CircuitField,
    pub(crate) z: C::CircuitField,
    pub(crate) mu: C::CircuitField,
    pub(crate) nu: C::CircuitField,
    pub(crate) mu_prime: C::CircuitField,
    pub(crate) nu_prime: C::CircuitField,
    pub(crate) x: C::CircuitField,
    pub(crate) alpha: C::CircuitField,
    pub(crate) u: C::CircuitField,
    /// Pre-endoscalar beta challenge. Effective beta is derived via endoscalar extraction.
    pub(crate) pre_beta: C::CircuitField,
}

impl<C: Cycle> Challenges<C> {
    pub(crate) fn new<'dr, D>(
        w: &Element<'dr, D>,
        y: &Element<'dr, D>,
        z: &Element<'dr, D>,
        mu: &Element<'dr, D>,
        nu: &Element<'dr, D>,
        mu_prime: &Element<'dr, D>,
        nu_prime: &Element<'dr, D>,
        x: &Element<'dr, D>,
        alpha: &Element<'dr, D>,
        u: &Element<'dr, D>,
        pre_beta: &Element<'dr, D>,
    ) -> Self
    where
        D: Driver<'dr, F = C::CircuitField, MaybeKind = Always<()>>,
    {
        Self {
            w: *w.value().take(),
            y: *y.value().take(),
            z: *z.value().take(),
            mu: *mu.value().take(),
            nu: *nu.value().take(),
            mu_prime: *mu_prime.value().take(),
            nu_prime: *nu_prime.value().take(),
            x: *x.value().take(),
            alpha: *alpha.value().take(),
            u: *u.value().take(),
            pre_beta: *pre_beta.value().take(),
        }
    }

    pub(crate) fn trivial() -> Self {
        Self {
            w: C::CircuitField::ZERO,
            y: C::CircuitField::ZERO,
            z: C::CircuitField::ZERO,
            mu: C::CircuitField::ZERO,
            nu: C::CircuitField::ZERO,
            mu_prime: C::CircuitField::ZERO,
            nu_prime: C::CircuitField::ZERO,
            x: C::CircuitField::ZERO,
            alpha: C::CircuitField::ZERO,
            u: C::CircuitField::ZERO,
            pre_beta: C::CircuitField::ZERO,
        }
    }
}

#[derive(Clone)]
pub(crate) struct InternalCircuits<C: Cycle, R: Rank> {
    pub(crate) hashes_1: RxTriple<C, R>,
    pub(crate) hashes_2: RxTriple<C, R>,
    pub(crate) inner_collapse: RxTriple<C, R>,
    pub(crate) outer_collapse: RxTriple<C, R>,
    pub(crate) compute_v: RxTriple<C, R>,
}
