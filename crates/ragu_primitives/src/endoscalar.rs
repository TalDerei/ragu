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

use alloc::vec::Vec;

use ragu_arithmetic::{
    Coeff, CurveAffine,
    ff::{Field, PrimeField, WithSmallOrderMulGroup},
};
use ragu_core::{
    Error, Result,
    drivers::{Driver, DriverValue, LinearExpression, emulator::Emulator},
    gadgets::Gadget,
    maybe::Maybe,
};

use crate::{
    Boolean, Element, NonzeroBank, Point,
    allocator::Allocator,
    promotion::Demoted,
    util::InternalMaybe,
    vec::{CollectFixed, ConstLen, FixedVec},
};

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

    /// Extracts an endoscalar from a random element in the field.
    pub fn extract<A: crate::allocator::Allocator<'dr, D>>(
        dr: &mut D,
        allocator: &mut A,
        elem: Element<'dr, D>,
    ) -> Result<Self>
    where
        D::F: WithSmallOrderMulGroup<3>,
    {
        let mut bits = Vec::with_capacity(u128::BITS as usize);
        let mut value = D::just(|| 0u128);
        let mut constant = D::F::ZERO;

        for i in 0..(u128::BITS as usize) {
            let (sqrt, bit) = D::try_just(|| {
                let value = *elem.value().take() + constant;

                if let Some(sqrt) = value.sqrt().into_option() {
                    Ok((sqrt, true))
                } else {
                    let sqrt = (value * D::F::MULTIPLICATIVE_GENERATOR)
                        .sqrt()
                        .into_option()
                        .expect("should produce a square if the other didn't");
                    Ok((sqrt, false))
                }
            })?
            .cast();

            value.as_mut().map(|v| {
                if *bit.snag() {
                    *v |= 1u128 << i
                }
            });

            let bit = constrain_extraction_bit(dr, allocator, &elem, constant, sqrt, bit)?;

            bits.push(Demoted::new(&bit)?);
            constant += D::F::ONE;
        }

        Ok(Endoscalar {
            bits: FixedVec::try_from(bits)?,
            value,
        })
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

/// Allocates and constrains a single endoscalar extraction bit.
///
/// Computes the `inverse` advice for [`constrain_extraction_bit_with_inverse`]
/// (the inverse of `elem + constant`, or zero when `bit` is true) and delegates.
/// Returns [`Error::InvalidWitness`] for a false `bit` at `elem + constant == 0`.
fn constrain_extraction_bit<'dr, D: Driver<'dr>, A: Allocator<'dr, D>>(
    dr: &mut D,
    allocator: &mut A,
    elem: &Element<'dr, D>,
    constant: D::F,
    sqrt: DriverValue<D, D::F>,
    bit: DriverValue<D, bool>,
) -> Result<Boolean<'dr, D>>
where
    D::F: WithSmallOrderMulGroup<3>,
{
    let inverse = D::try_just(|| {
        let shifted = *elem.value().take() + constant;
        if *bit.snag() {
            Ok(D::F::ZERO)
        } else {
            shifted
                .invert()
                .into_option()
                .ok_or_else(|| Error::InvalidWitness("endoscalar false bit at zero".into()))
        }
    })?;

    constrain_extraction_bit_with_inverse(dr, allocator, elem, constant, sqrt, bit, inverse)
}

/// Constrains a single endoscalar extraction bit given the `inverse` advice,
/// emitting the square and nonzero constraints and returning `bit`'s [`Boolean`].
///
/// `bit` records whether `elem + constant` is a quadratic residue, witnessed by
/// `sqrt` (a root of `elem + constant`, or of
/// `(elem + constant) * MULTIPLICATIVE_GENERATOR` when `bit` is false). The
/// `inverse` forces a false `bit` to prove `elem + constant != 0`,
/// disambiguating the zero case where both branches square to zero and the bit
/// would otherwise be free.
///
/// Split from [`constrain_extraction_bit`] so tests can forge `inverse` and
/// confirm the false-bit-at-zero witness is rejected.
fn constrain_extraction_bit_with_inverse<'dr, D: Driver<'dr>, A: Allocator<'dr, D>>(
    dr: &mut D,
    allocator: &mut A,
    elem: &Element<'dr, D>,
    constant: D::F,
    sqrt: DriverValue<D, D::F>,
    bit: DriverValue<D, bool>,
    inverse: DriverValue<D, D::F>,
) -> Result<Boolean<'dr, D>>
where
    D::F: WithSmallOrderMulGroup<3>,
{
    let bit = Boolean::alloc(dr, allocator, bit)?;
    let constant_elem = Element::constant(dr, constant);
    let shifted = elem.add(dr, &constant_elem);
    let (_, square) = Element::alloc_square(dr, sqrt)?;
    let vb = elem.mul(dr, &bit.element())?;

    // Force `bit = 1` when `elem + constant == 0`: there the square constraint
    // below sends `square` to zero for either bit, so it cannot pin the bit and
    // a prover could forge a non-residue claim (`bit = 0`). The inverse trick
    // rules this out:
    //
    // - shifted * inverse = is_not_zero
    // - is_not_zero = 1 - bit
    //
    // When `bit == 0` these force `shifted = elem + constant` to be nonzero,
    // rejecting the zero case; when `bit == 1` they reduce to
    // `shifted * inverse = 0`, which `inverse = 0` always satisfies (complete).
    let (shifted_wire, _, is_not_zero) = dr.mul(|| {
        Ok((
            Coeff::Arbitrary(*shifted.value().take()),
            Coeff::Arbitrary(*inverse.snag()),
            bit.value().not().coeff().take(),
        ))
    })?;
    dr.enforce_equal(&shifted_wire, shifted.wire())?;
    dr.enforce_zero(|lc| lc.add(&is_not_zero).sub(&D::ONE).add(bit.wire()))?;

    // Enforce that the square is equal to
    //     (elem + constant) if bit == 1
    //     (elem + constant) * MULTIPLICATIVE_GENERATOR if bit == 0
    // This is done by enforcing the constraint:
    //
    //     square = bit * (elem + constant)
    //            + (1 - bit) * ((elem + constant) * MULTIPLICATIVE_GENERATOR)
    //
    //            = constant * MULTIPLICATIVE_GENERATOR
    //            + bit * (constant * (1 - MULTIPLICATIVE_GENERATOR))
    //            + elem * MULTIPLICATIVE_GENERATOR
    //            + vb * (1 - MULTIPLICATIVE_GENERATOR)
    let coeff_2 = D::F::MULTIPLICATIVE_GENERATOR;
    let coeff_3 = D::F::ONE - D::F::MULTIPLICATIVE_GENERATOR;
    dr.enforce_zero(|lc| {
        lc.add_term(&D::ONE, (constant * coeff_2).into())
            .add_term(bit.wire(), (constant * coeff_3).into())
            .add_term(elem.wire(), coeff_2.into())
            .add_term(vb.wire(), coeff_3.into())
            .sub(square.wire())
    })?;

    Ok(bit)
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

/// Extracts an endoscalar from a random field element.
///
/// Given a random output of a secure algebraic hash function, this extracts
/// `k` bits of "randomness" from the value by checking whether `value + i`
/// is a quadratic residue for each bit position `i`.
pub fn extract_endoscalar<F: PrimeField + WithSmallOrderMulGroup<3>>(value: F) -> u128 {
    Emulator::emulate_wireless(value, |dr, witness| {
        let elem = Element::alloc(dr, &mut (), witness)?;
        let endo = Endoscalar::extract(dr, &mut (), elem)?;
        Ok(*endo.value.snag())
    })
    .expect("wireless emulation should not fail")
}

#[cfg(test)]
mod tests {
    use ragu_arithmetic::{
        CurveAffine, CurveExt,
        ff::{Field, PrimeField, WithSmallOrderMulGroup},
        group::{CurveAffine as _, Group},
        rand::RngExt,
    };
    use ragu_core::{Result, drivers::Driver};
    use ragu_pasta::{EpAffine, Fp};

    use super::{Element, Endoscalar, Maybe, Point};
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

    /// Independent reference implementation of endoscalar extraction.
    ///
    /// Unlike [`super::extract_endoscalar`], which drives the gadget through the
    /// emulator, this recomputes the bits directly from field arithmetic, so it
    /// is unlikely to share a synthesis bug.
    fn native_extract<F: PrimeField + WithSmallOrderMulGroup<3>>(value: F) -> u128 {
        let mut endoscalar = 0u128;
        let mut constant = F::ZERO;

        for i in 0..(u128::BITS as usize) {
            if (value + constant).sqrt().into_option().is_some() {
                endoscalar |= 1u128 << i;
            }
            constant += F::ONE;
        }

        endoscalar
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
        let r = Fp::random(&mut ragu_arithmetic::rand::rng());
        let extracted = extract(r).value;

        Simulator::<Fp>::simulate((r, extracted, p), |dr, witness| {
            let (r, extracted, p) = witness.cast();
            let p = Point::alloc(dr, p)?;
            let allocator = &mut Standard::new();
            let r = Element::alloc(dr, allocator, r)?;
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

    /// Regression test for the under-constrained zero case: at `elem + i == 0`
    /// the extracted bit must be set, matching the native oracle.
    #[test]
    fn test_extract_exceptional_zero_bits_match_native() -> Result<()> {
        for i in 0..(u128::BITS as usize) {
            let r = -Fp::from(i as u64);
            let expected = native_extract(r);

            assert_eq!(
                (expected >> i) & 1u128,
                1u128,
                "native extraction must set the zero bit for i={i}"
            );

            Simulator::<Fp>::simulate((r, expected), |dr, witness| {
                let (r, expected) = witness.cast();
                let allocator = &mut Standard::new();
                let r = Element::alloc(dr, allocator, r)?;
                let extracted = Endoscalar::extract(dr, allocator, r)?;

                assert_eq!(*extracted.value.snag(), *expected.snag());

                Ok(())
            })?;
        }

        Ok(())
    }

    /// Regression test for the under-constrained zero case: a forged
    /// `bit = false` witness at `elem + i == 0` must be rejected by the nonzero
    /// constraint.
    #[test]
    fn test_extract_rejects_false_zero_bits() -> Result<()> {
        for i in 0..(u128::BITS as usize) {
            let r = -Fp::from(i as u64);
            let result = Simulator::<Fp>::simulate(r, |dr, witness| {
                let allocator = &mut Standard::new();
                let elem = Element::alloc(dr, allocator, witness)?;

                super::constrain_extraction_bit_with_inverse(
                    dr,
                    allocator,
                    &elem,
                    Fp::from(i as u64),
                    Simulator::<Fp>::just(|| Fp::ZERO),
                    Simulator::<Fp>::just(|| false),
                    Simulator::<Fp>::just(|| Fp::ZERO),
                )?;

                Ok(())
            });

            assert!(
                result.is_err(),
                "false extraction bit at elem + i = 0 must be rejected for i={i}"
            );
        }

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
