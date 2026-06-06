//! Implements logic for endoscaling, as introduced in
//! [Halo](https://eprint.iacr.org/2019/1021).
//!
//! An endoscalar is the catchy name for a small binary string that is used to
//! perform elliptic curve scalar multiplication on curves that have an
//! efficient endomorphism attached. By producing endoscalars as challenges and
//! applying an appropriate algorithm, points on an elliptic curve can be
//! multiplied by equally "random" challenge scalars more efficiently within a
//! circuit than an arbitrary scalar.
//!
//! This module provides an implementation of the scaling operation for curves
//! which support the endomorphism, and an implementation of the algorithm for
//! recovering the effective scalar that an endoscalar maps to for a particular
//! prime field.

use ragu_arithmetic::{
    Coeff, CurveAffine,
    ff::{Field, PrimeField, WithSmallOrderMulGroup},
};
use ragu_core::{
    Result,
    drivers::{Driver, DriverTypes, DriverValue, emulator::Emulator},
    gadgets::{Gadget, Kind},
    maybe::{Always, Maybe},
    routines::{Prediction, Routine},
};

use crate::{
    Boolean, Element, NonzeroBank, Point, Simulator,
    boolean::decompose,
    promotion::Demoted,
    vec::{CollectFixed, ConstLen, FixedVec},
};

/// A transcript challenge pre-validated for endoscalar extraction.
///
/// Carries the precondition required by [`Endoscalar::extract`]: the element's
/// canonical representative is below `2^CAPACITY`, so it admits a canonical
/// `CAPACITY`-bit decomposition with no separate in-circuit canonicity check.
#[derive(Gadget)]
pub struct EndoscalarChallenge<'dr, D: Driver<'dr>> {
    #[ragu(gadget)]
    elem: Element<'dr, D>,
}

impl<'dr, D: Driver<'dr>> EndoscalarChallenge<'dr, D> {
    /// Validates an in-range element as an endoscalar challenge.
    ///
    /// The single-attempt constructor: it succeeds only when `elem` is
    /// already in range (canonical representative below `2^CAPACITY`).
    /// Validation runs through a [`Routine`], so proving drivers emulate the
    /// decomposition before handing back the typed challenge; an out-of-range
    /// element makes that decomposition unsatisfiable and surfaces as [`Err`].
    ///
    /// It serves the in-circuit verifier path, where an honest prover has
    /// already ground the challenge into range and it is only re-derived
    /// (see the `compute_v` internal circuit). Native provers sampling a fresh
    /// challenge must use [`sample`] instead, which owns the rejection-sampling
    /// loop and so cannot be skipped.
    ///
    /// # Errors
    ///
    /// Returns an error if the decomposition is unsatisfiable
    /// (`elem >= 2^CAPACITY`) or the driver fails to synthesize it.
    ///
    /// [`sample`]: EndoscalarChallenge::sample
    pub fn from_element(dr: &mut D, elem: Element<'dr, D>) -> Result<Self>
    where
        D::F: PrimeField,
    {
        dr.routine(ValidateEndoscalarChallenge, elem)
    }

    /// Attempts to validate an element as an endoscalar challenge, reporting an
    /// out-of-range element as `Ok(None)` rather than an error.
    ///
    /// The rejection-sampling primitive behind [`sample`]: it separates the
    /// *expected* out-of-range outcome (`Ok(None)`, a retry signal) from a
    /// *genuine* synthesis failure (`Err`, to propagate, not retry). The range
    /// check is the same canonical decomposition enforced by
    /// [`Endoscalar::extract`].
    ///
    /// # Completeness
    ///
    /// Requires the element's witness, enforced by the `MaybeKind = Always<()>`
    /// bound; it is the prover-side counterpart to [`from_element`].
    ///
    /// # Errors
    ///
    /// Errors only on a genuine synthesis failure while validating an in-range
    /// element; an out-of-range element is reported as `Ok(None)`.
    ///
    /// [`sample`]: EndoscalarChallenge::sample
    /// [`from_element`]: EndoscalarChallenge::from_element
    pub(crate) fn try_from_element(dr: &mut D, elem: Element<'dr, D>) -> Result<Option<Self>>
    where
        D: DriverTypes<MaybeKind = Always<()>>,
        D::F: PrimeField,
    {
        // Classify the candidate by value first, so an out-of-range challenge
        // never reaches the decomposition routine (which would conflate it with
        // a genuine synthesis error). Only in-range challenges are validated.
        if !endoscalar_in_range(**elem.value().snag()) {
            return Ok(None);
        }

        Self::from_element(dr, elem).map(Some)
    }

    /// Produces a validated endoscalar challenge by rejection sampling.
    ///
    /// `produce` is invoked to (re)sample fresh randomness, returning a
    /// candidate challenge [`Element`] together with a `payload` of side state
    /// derived from it. The candidate is validated by `try_from_element`: on
    /// acceptance the challenge and its payload are returned; on an
    /// out-of-range candidate `produce` is called again with fresh randomness.
    ///
    /// Baking the loop into the constructor makes it impossible to obtain a
    /// challenge without having ground it into range: every native challenge
    /// flows through this single point.
    ///
    /// # Completeness
    ///
    /// With uniformly random field elements each attempt succeeds with
    /// overwhelming probability (about `1 - 2^-129` over the Pasta fields), so
    /// the loop terminates after a handful of iterations in expectation.
    ///
    /// # Errors
    ///
    /// A genuine synthesis failure in `produce` or in validating an in-range
    /// candidate propagates immediately; the loop retries only on the expected
    /// out-of-range condition and so cannot spin on a real error.
    pub fn sample<T>(
        dr: &mut D,
        mut produce: impl FnMut(&mut D) -> Result<(Element<'dr, D>, T)>,
    ) -> Result<(Self, T)>
    where
        D: DriverTypes<MaybeKind = Always<()>>,
        D::F: PrimeField,
    {
        loop {
            let (elem, payload) = produce(dr)?;
            if let Some(challenge) = Self::try_from_element(dr, elem)? {
                return Ok((challenge, payload));
            }
        }
    }

    /// Extracts the native endoscalar from this validated challenge.
    ///
    /// Returns the low 128 bits of the challenge's canonical bit
    /// decomposition, the native, wireless counterpart to
    /// [`Endoscalar::extract`]. Because an [`EndoscalarChallenge`] has already
    /// passed range validation, extraction is infallible: this type's invariant
    /// upholds the precondition of [`extract_endoscalar`].
    ///
    /// # Completeness
    ///
    /// Requires the challenge's witness, enforced by the
    /// `MaybeKind = Always<()>` bound; intended for native provers that
    /// constructed the challenge via [`sample`].
    ///
    /// [`sample`]: EndoscalarChallenge::sample
    pub fn extract_native(&self) -> u128
    where
        D: DriverTypes<MaybeKind = Always<()>>,
        D::F: PrimeField,
    {
        extract_endoscalar(**self.elem.value().snag())
    }

    /// Returns the underlying field element.
    pub fn element(&self) -> &Element<'dr, D> {
        &self.elem
    }
}

#[derive(Clone, Copy)]
struct ValidateEndoscalarChallenge;

impl<F: PrimeField> Routine<F> for ValidateEndoscalarChallenge {
    type Input = Kind![F; Element<'_, _>];
    type Output = Kind![F; EndoscalarChallenge<'_, _>];
    type Aux<'dr> = ();

    fn execute<'dr, D: Driver<'dr, F = F>>(
        &self,
        _dr: &mut D,
        input: Element<'dr, D>,
        _aux: DriverValue<D, Self::Aux<'dr>>,
    ) -> Result<EndoscalarChallenge<'dr, D>> {
        Ok(EndoscalarChallenge { elem: input })
    }

    fn predict<'dr, D: Driver<'dr, F = F, Wire = ()>>(
        &self,
        _dr: &mut D,
        input: &Element<'dr, D>,
    ) -> Result<Prediction<EndoscalarChallenge<'dr, D>, DriverValue<D, Self::Aux<'dr>>>> {
        let value = input.value();
        let aux = D::try_just(|| validate_endoscalar_challenge(**value.snag()))?;

        Ok(Prediction::Known(
            EndoscalarChallenge {
                elem: input.clone(),
            },
            aux,
        ))
    }
}

/// Reports whether `value` lies in the range admitted by an endoscalar
/// challenge (canonical representative below `2^CAPACITY`).
///
/// A pure, wireless mirror of the canonical bit decomposition enforced in
/// circuit by [`Endoscalar::extract`]: it recomposes the low `CAPACITY` bits
/// of the canonical representative and checks whether they reproduce `value`,
/// so it is `true` exactly when that in-circuit decomposition is satisfiable.
///
/// Unlike the in-circuit validation, an out-of-range value is reported as
/// `false` rather than as an error, so callers performing rejection sampling
/// can distinguish the expected out-of-range outcome from a genuine synthesis
/// failure. This is the range predicate used by
/// `EndoscalarChallenge::try_from_element`.
pub fn endoscalar_in_range<F: PrimeField>(value: F) -> bool {
    let repr = value.to_repr();

    // Recompose the low CAPACITY bits exactly as `decompose` does, then compare
    // against the original value. The two agree iff no bit at index >= CAPACITY
    // is set, i.e. iff `value < 2^CAPACITY`.
    let mut acc = F::ZERO;
    let mut gain = F::ONE;
    for i in 0..(F::CAPACITY as usize) {
        if (repr.as_ref()[i / 8] >> (i % 8)) & 1 == 1 {
            acc += gain;
        }
        gain = gain.double();
    }

    acc == value
}

/// Validates the native precondition for an endoscalar challenge.
///
/// Runs the same canonical decomposition as
/// [`EndoscalarChallenge::from_element`] under the simulator. It succeeds
/// exactly when `value` is in the range admitted by [`Endoscalar::extract`]
/// (equivalently, when [`endoscalar_in_range`] is `true`), and backs the
/// emulate-first check in the [`ValidateEndoscalarChallenge`] routine.
pub(crate) fn validate_endoscalar_challenge<F: PrimeField>(value: F) -> Result<()> {
    Simulator::simulate(value, |dr, value| {
        let elem = Element::alloc(dr, &mut (), value)?;
        decompose(dr, &mut (), &elem)?;
        Ok(())
    })?;

    Ok(())
}

/// Represents a challenge used to scale elliptic curve points.
#[derive(Gadget)]
pub struct Endoscalar<'dr, D: Driver<'dr>> {
    /// The bits of this endoscalar in little-endian order.
    #[ragu(gadget)]
    bits: FixedVec<Demoted<'dr, D, Boolean<'dr, D>>, ConstLen<{ u128::BITS as usize }>>,

    /// The represented endoscalar witness value in compact representation.
    #[ragu(value)]
    value: DriverValue<D, u128>,
}

impl<'dr, D: Driver<'dr>> Endoscalar<'dr, D> {
    /// Allocate an endoscalar with the provided witness value.
    pub fn alloc(dr: &mut D, value: DriverValue<D, u128>) -> Result<Self> {
        let bits = (0..u128::BITS as usize)
            .map(|i| {
                let bit = Boolean::alloc(
                    dr,
                    &mut (),
                    value.as_ref().map(|v| (*v >> i) & 1u128 == 1u128),
                )?;
                Demoted::new(&bit)
            })
            .try_collect_fixed()?;

        Ok(Endoscalar { bits, value })
    }

    /// Returns an iterator over the bits in this endoscalar, little endian order.
    pub fn bits(&self) -> impl Iterator<Item = Boolean<'dr, D>> {
        let mut bits = self
            .value
            .as_ref()
            .map(|v| (0..(u128::BITS as usize)).map(move |i| (*v >> i) & 1u128 == 1u128));

        self.bits.iter().map(move |demoted_bit| {
            demoted_bit.promote(bits.as_mut().map(|bits| bits.next().unwrap()))
        })
    }

    /// Extracts an endoscalar from a validated challenge.
    ///
    /// The endoscalar is the low 128 bits of the challenge's canonical bit
    /// decomposition. The element is decomposed in full, so those 128 bits are
    /// uniquely determined by it.
    ///
    /// # Completeness
    ///
    /// The decomposition is satisfiable only for values below `2^CAPACITY`.
    /// [`EndoscalarChallenge`] establishes exactly that precondition, so every
    /// validated challenge extracts; an out-of-range value would make the
    /// constraints unsatisfiable.
    pub fn extract<A: crate::allocator::Allocator<'dr, D>>(
        dr: &mut D,
        allocator: &mut A,
        challenge: EndoscalarChallenge<'dr, D>,
    ) -> Result<Self>
    where
        D::F: PrimeField,
    {
        let elem = challenge.elem;
        let bits = decompose(dr, allocator, &elem)?;

        let value = elem.value().map(|v| {
            let repr = v.to_repr();
            let mut acc = 0u128;
            for i in 0..(u128::BITS as usize) {
                if (repr.as_ref()[i / 8] >> (i % 8)) & 1 == 1 {
                    acc |= 1u128 << i;
                }
            }
            acc
        });

        let bits = bits
            .iter()
            .take(u128::BITS as usize)
            .map(|bit| Demoted::new(bit))
            .try_collect_fixed()?;

        Ok(Endoscalar { bits, value })
    }

    /// Scale a point by the endoscalar.
    ///
    /// Endoscalars in this library are $2n = 128$ bits long, and this algorithm
    /// is proven to be injective for all prime fields of size greater than
    /// $4(2^n - 1)^2$, which is comfortably safe for the Pasta fields because
    /// they are larger than $1361129467683753853705924477137396432900$. See
    /// `qa/lean/Ragu/Contrib/EndoscalarProof.lean`.
    pub fn group_scale<C: CurveAffine<Base = D::F>>(
        &self,
        dr: &mut D,
        p: &Point<'dr, D, C>,
    ) -> Result<Point<'dr, D, C>> {
        // Soundness: every `add_incomplete` and `double_and_add_incomplete`
        // call below requires `x_1 != x_0`. Appendix C of the Halo paper
        // (<https://eprint.iacr.org/2019/1021>) proves no such collision occurs
        // for endoscalars well beyond 128 bits on the Pasta curves Ragu uses,
        // so the bank is created in unchecked mode.
        //
        // TODO(ebfull): The no-collision argument above is a property of the
        // curve / endoscalar interaction that the `Cycle` API should attest to
        // at compile time, so callers can verify it holds for their choice of
        // curve rather than relying on this ad-hoc local justification.
        let mut bank = NonzeroBank::new_unchecked();

        let mut acc = p.endo(dr).add_incomplete(dr, p, &mut bank)?.double(dr)?;
        let mut bits = self.bits();

        // Each iteration consumes a pair of bits; u128::BITS is even.
        for _ in 0..(u128::BITS as usize / 2) {
            let negate_bit = bits.next().unwrap();
            let endo_bit = bits.next().unwrap();

            let q = p
                .conditional_negate(dr, &negate_bit)?
                .conditional_endo(dr, &endo_bit)?;
            acc = acc.double_and_add_incomplete(dr, &q, &mut bank)?;
        }

        Ok(acc)
    }

    /// Lifts this endoscalar to a field element (scales $1$ by the endoscalar).
    pub fn lift(&self, dr: &mut D) -> Result<Element<'dr, D>>
    where
        D::F: WithSmallOrderMulGroup<3>,
    {
        let mut constant_term = (D::F::ZETA + D::F::ONE).double();
        let coeffs = [
            -D::F::from(2),
            D::F::ZETA - D::F::ONE,
            (D::F::ONE - D::F::ZETA).double(),
        ];

        let mut acc = Element::zero(dr);
        let mut bits = self.bits();

        // Each iteration consumes a pair of bits; u128::BITS is even.
        for _ in 0..(u128::BITS as usize / 2) {
            let n = bits.next().unwrap();
            let e = bits.next().unwrap();
            let ne = n.and(dr, &e)?;

            acc = acc.double(dr);
            constant_term = constant_term.double();
            constant_term += D::F::ONE;

            let n = n.element().scale(dr, Coeff::Arbitrary(coeffs[0]));
            let e = e.element().scale(dr, Coeff::Arbitrary(coeffs[1]));
            let ne = ne.element().scale(dr, Coeff::Arbitrary(coeffs[2]));

            acc = acc.add(dr, &n);
            acc = acc.add(dr, &e);
            acc = acc.add(dr, &ne);
        }

        let tmp = Element::constant(dr, constant_term);
        acc = acc.add(dr, &tmp);

        Ok(acc)
    }
}

/// Lifts an endoscalar to a field element (computes the effective scalar).
///
/// This implements [Algorithm 2, \[BGH19\]](https://eprint.iacr.org/2019/1021)
/// and is the native counterpart to [`Endoscalar::lift`].
pub fn lift_endoscalar<F: WithSmallOrderMulGroup<3>>(endo: u128) -> F {
    let mut acc = (F::ZETA + F::ONE).double();
    for i in 0..(u128::BITS as usize / 2) {
        let bits = endo >> (i << 1);
        let mut tmp = F::ONE;
        if bits & 0b01u128 != 0u128 {
            tmp = -tmp;
        }
        if bits & 0b10u128 != 0u128 {
            tmp *= F::ZETA;
        }
        acc = acc.double() + tmp;
    }
    acc
}

/// Extracts an endoscalar from a validated field element.
///
/// Returns the low 128 bits of the element's canonical bit decomposition, the
/// native counterpart to [`Endoscalar::extract`].
///
/// A low-level helper: prefer [`EndoscalarChallenge::extract_native`], which
/// upholds the precondition below as a type invariant. This function is exposed
/// directly only for native setup paths with no [`EndoscalarChallenge`] in
/// scope (e.g. the trivial proof construction over a constant that is in range
/// by inspection).
///
/// # Completeness
///
/// Infallible when `value` has already passed rejection sampling
/// (`value < 2^CAPACITY`, equivalently `endoscalar_in_range` is `true`).
/// Callers must enforce that first; an out-of-range value makes the in-circuit
/// [`EndoscalarChallenge`] validation fail before [`Endoscalar::extract`] is
/// reachable.
///
/// # Panics
///
/// Panics if `value` has not passed endoscalar challenge validation.
pub fn extract_endoscalar<F: PrimeField>(value: F) -> u128 {
    Emulator::emulate_wireless(value, |dr, witness| {
        let elem = Element::alloc(dr, &mut (), witness)?;
        let challenge = EndoscalarChallenge::from_element(dr, elem)?;
        let endo = Endoscalar::extract(dr, &mut (), challenge)?;
        Ok(*endo.value.snag())
    })
    .expect("endoscalar challenge should satisfy value < 2^CAPACITY")
}

#[cfg(test)]
mod tests {
    use ragu_arithmetic::{
        CurveAffine, CurveExt,
        ff::{Field, PrimeField, WithSmallOrderMulGroup},
        group::{CurveAffine as _, Group},
        rand::RngExt,
    };
    use ragu_core::Result;
    use ragu_pasta::{EpAffine, Fp};

    use super::{Element, Endoscalar, EndoscalarChallenge, Maybe, Point};
    use crate::{Simulator, allocator::Standard};

    pub struct EndoscalarTest {
        pub value: u128,
    }

    impl EndoscalarTest {
        /// Implements [Algorithm 1, \[BGH19\]](https://eprint.iacr.org/2019/1021).
        pub fn scale<C: CurveAffine>(&self, p: &C) -> C {
            let p = p.to_curve();
            let mut acc = (p.endo() + p).double();
            for bits in (0..(u128::BITS as usize / 2)).map(|i| self.value >> (i << 1)) {
                let mut s = p;
                if bits & 0b01u128 != 0u128 {
                    s = -s;
                }
                if bits & 0b10u128 != 0u128 {
                    s = s.endo();
                }

                acc = (acc + s) + acc;
            }
            acc.into()
        }

        /// Implements [Algorithm 2, \[BGH19\]](https://eprint.iacr.org/2019/1021).
        pub fn lift<F: WithSmallOrderMulGroup<3>>(&self) -> F {
            super::lift_endoscalar(self.value)
        }
    }

    pub fn extract<F: PrimeField + WithSmallOrderMulGroup<3>>(value: F) -> EndoscalarTest {
        EndoscalarTest {
            value: super::extract_endoscalar(value),
        }
    }

    #[test]
    #[allow(clippy::useless_conversion)]
    fn test_endoscaling_consistency() {
        use ragu_arithmetic::group::CurveAffine as _;
        use ragu_pasta::{EpAffine, Fq};

        let p = EpAffine::generator();
        let e = EndoscalarTest {
            value: 206786806484900909362154774549736492353u128,
        };
        let scaled = e.scale(&p);
        let expected: EpAffine = (p * e.lift::<Fq>()).into();

        assert_eq!(scaled, expected);
    }

    #[test]
    fn test_extract() -> Result<()> {
        let p = EpAffine::generator();
        let r = loop {
            let r = Fp::random(&mut ragu_arithmetic::rand::rng());
            if super::validate_endoscalar_challenge(r).is_ok() {
                break r;
            }
        };
        let extracted = extract(r).value;

        Simulator::<Fp>::simulate((r, extracted, p), |dr, witness| {
            let (r, extracted, p) = witness.cast();
            let p = Point::alloc(dr, p)?;
            let allocator = &mut Standard::new();
            let r = Element::alloc(dr, allocator, r)?;
            let r = EndoscalarChallenge::from_element(dr, r)?;
            let my_extracted = Endoscalar::extract(dr, &mut (), r)?;
            let allocated = Endoscalar::alloc(dr, extracted)?;

            assert_eq!(my_extracted.value.snag(), allocated.value.snag());

            let a = my_extracted.group_scale(dr, &p)?;
            let b = allocated.group_scale(dr, &p)?;
            assert_eq!(a.value().take(), b.value().take());

            Ok(())
        })?;

        Ok(())
    }

    #[test]
    fn test_endoscalar_challenge_rejects_out_of_range() {
        assert!(super::validate_endoscalar_challenge(-Fp::ONE).is_err());

        let result = Simulator::<Fp>::simulate(-Fp::ONE, |dr, witness| {
            let elem = Element::alloc(dr, &mut (), witness)?;
            EndoscalarChallenge::from_element(dr, elem)?;
            Ok(())
        });

        assert!(result.is_err());
    }

    /// The pure-value range predicate must agree with the simulator-based
    /// decomposition check for every value, so that rejection sampling using
    /// `endoscalar_in_range` never disagrees with what the circuit enforces.
    #[test]
    fn test_in_range_matches_validation() {
        let largest_in_range = {
            let mut acc = Fp::ZERO;
            for _ in 0..(Fp::CAPACITY as usize) {
                acc = acc.double() + Fp::ONE;
            }
            acc
        };

        let cases = [
            Fp::ZERO,
            Fp::ONE,
            Fp::from(0x0123_4567_89ab_cdefu64),
            largest_in_range,
            largest_in_range + Fp::ONE, // first out-of-range value
            -Fp::ONE,                   // p - 1, out of range
        ];

        for value in cases {
            assert_eq!(
                super::endoscalar_in_range(value),
                super::validate_endoscalar_challenge(value).is_ok(),
                "in-range predicate disagreed with validation",
            );
        }

        // Random sampling: the predicate must match validation on fresh draws,
        // exercising the overwhelmingly-in-range path.
        for _ in 0..32 {
            let value = Fp::random(&mut ragu_arithmetic::rand::rng());
            assert_eq!(
                super::endoscalar_in_range(value),
                super::validate_endoscalar_challenge(value).is_ok(),
            );
        }
    }

    /// `sample` grinds an out-of-range candidate away and returns the accepted
    /// candidate together with its payload; `extract_native` then matches the
    /// in-circuit extraction.
    #[test]
    fn test_sample_grinds_until_in_range() -> Result<()> {
        use ragu_core::drivers::Driver;

        // Feed one out-of-range candidate followed by an in-range one. `sample`
        // must reject the first, accept the second, and thread the payload
        // through unchanged.
        let in_range = Fp::from(0x0123_4567_89ab_cdefu64);

        Simulator::<Fp>::simulate(in_range, |dr, in_range| {
            let in_range = in_range.take();
            let candidates = [(-Fp::ONE, 7u32), (in_range, 9u32)];
            let mut attempt = 0usize;

            let (challenge, payload) = EndoscalarChallenge::sample(dr, |dr| {
                let (value, tag) = candidates[attempt];
                attempt += 1;
                let elem = Element::alloc(dr, &mut (), Simulator::<Fp>::just(|| value))?;
                Ok((elem, tag))
            })?;

            assert_eq!(attempt, 2, "expected exactly one rejection");
            assert_eq!(payload, 9, "accepted candidate's payload must be returned");
            assert_eq!(
                challenge.extract_native(),
                super::extract_endoscalar(in_range),
            );

            Ok(())
        })?;

        Ok(())
    }

    /// A genuine error from `produce` propagates immediately instead of being
    /// retried: the rejection loop retries only on the expected out-of-range
    /// outcome, never on a real synthesis failure.
    #[test]
    fn test_sample_propagates_produce_error() -> Result<()> {
        Simulator::<Fp>::simulate((), |dr, _| {
            let mut calls = 0usize;
            let outcome = EndoscalarChallenge::sample(dr, |_dr| {
                calls += 1;
                Result::<(Element<'_, _>, ())>::Err(ragu_core::Error::InvalidWitness(
                    "produce failure".into(),
                ))
            });

            assert!(outcome.is_err(), "produce error must surface as Err");
            assert_eq!(calls, 1, "produce error must not be retried");

            Ok(())
        })?;

        Ok(())
    }

    /// `try_from_element` classifies an out-of-range element as `Ok(None)` (the
    /// retry signal) and an in-range element as `Ok(Some(_))`, pinning the
    /// acceptance boundary at `2^CAPACITY`.
    #[test]
    fn test_try_from_element_classifies_range() -> Result<()> {
        let largest_in_range = {
            let mut acc = Fp::ZERO;
            for _ in 0..(Fp::CAPACITY as usize) {
                acc = acc.double() + Fp::ONE;
            }
            acc
        };

        let check = |value: Fp, expect_in_range: bool| -> Result<()> {
            Simulator::<Fp>::simulate(value, |dr, value| {
                let elem = Element::alloc(dr, &mut (), value)?;
                let classified = EndoscalarChallenge::try_from_element(dr, elem)?;
                assert_eq!(classified.is_some(), expect_in_range);
                Ok(())
            })?;
            Ok(())
        };

        check(Fp::ZERO, true)?;
        check(largest_in_range, true)?; // 2^CAPACITY - 1, the largest in range
        check(largest_in_range + Fp::ONE, false)?; // 2^CAPACITY, first out of range
        check(-Fp::ONE, false)?; // p - 1, out of range

        Ok(())
    }

    #[test]
    fn test_endoscaling() -> Result<()> {
        let p = EpAffine::generator();
        let r: u128 = ragu_arithmetic::rand::rng().random();
        let expected = EndoscalarTest { value: r }.scale(&p);

        Simulator::simulate((p, r), |dr, witness| {
            let (p, r) = witness.cast();
            let p = Point::alloc(dr, p.clone())?;
            let r = Endoscalar::alloc(dr, r.clone())?;

            dr.reset();
            assert_eq!(r.group_scale(dr, &p)?.value().take(), expected);
            assert_eq!(dr.num_gates(), 7 * (1 + (u128::BITS as usize / 2)));

            Ok(())
        })?;

        Ok(())
    }

    #[test]
    fn test_endoscalar_lift() -> Result<()> {
        let r: u128 = ragu_arithmetic::rand::rng().random();
        let expected: Fp = EndoscalarTest { value: r }.lift();

        Simulator::<Fp>::simulate(r, |dr, witness| {
            let r = Endoscalar::alloc(dr, witness)?;
            let s = r.lift(dr)?;

            assert_eq!(*s.value().take(), expected);

            Ok(())
        })?;

        Ok(())
    }
}
