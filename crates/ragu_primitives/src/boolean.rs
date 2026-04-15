//! Boolean gadget for constrained binary values.
//!
//! Provides the [`Boolean`] type representing a wire constrained to be zero or
//! one, with logical operations implemented as circuit constraints.

use alloc::vec::Vec;
use core::marker::PhantomData;

use ff::{Field, PrimeField};
use ragu_arithmetic::Coeff;
use ragu_core::{
    Result,
    convert::WireMap,
    drivers::{Driver, DriverValue, LinearExpression},
    gadgets::{Bound, Gadget, GadgetKind, Kind},
    maybe::Maybe,
};

#[cfg(test)]
use crate::allocator::{PoolAllocator, SimpleAllocator};
use crate::{
    Element, GadgetExt,
    consistent::Consistent,
    io::{Buffer, Write},
    promotion::{Demoted, Promotion},
    util::InternalMaybe,
    vec::{CollectFixed, FixedVec, Len},
};

/// Represents a wire that is constrained to be zero or one, along with its
/// corresponding [`bool`] value.
#[derive(Gadget)]
pub struct Boolean<'dr, D: Driver<'dr>> {
    /// The wire constrained to hold either `0` or `1` in the scalar field.
    #[ragu(wire)]
    wire: D::Wire,

    /// The witness value of this boolean.
    #[ragu(value)]
    value: DriverValue<D, bool>,
}

impl<'dr, D: Driver<'dr>> Boolean<'dr, D> {
    /// Allocates a boolean with the provided witness value.
    ///
    /// This costs one gate and two constraints.
    pub fn alloc<A: crate::allocator::Allocator<'dr, D>>(
        dr: &mut D,
        allocator: &mut A,
        value: DriverValue<D, bool>,
    ) -> Result<Self> {
        let complement = value.not();
        let (a, b, c, extra) =
            dr.gate(|| Ok((value.coeff().take(), complement.coeff().take(), Coeff::Zero)))?;

        // Enforce c = 0, so the gate constraint becomes a * b = 0.
        dr.enforce_zero(|lc| lc.add(&c))?;

        // Enforce a + b = 1. Together with a * b = 0,
        // this gives a(1 - a) = 0, so a is zero or one.
        dr.enforce_zero(|lc| lc.add(&D::ONE).sub(&a).sub(&b))?;

        // The gate's spare $D$ wire is donated to `allocator`.
        allocator.donate(extra);

        Ok(Boolean { value, wire: a })
    }

    /// Computes the NOT of this boolean. This is "free" in the circuit model.
    pub fn not(&self, dr: &mut D) -> Self {
        // The wire w is transformed into 1 - w, its logical NOT.
        let wire = dr.add(|lc| lc.add(&D::ONE).sub(self.wire()));
        let value = self.value().not();
        Boolean { wire, value }
    }

    /// Computes the AND of two booleans. This costs one gate and two
    /// constraints.
    pub fn and(&self, dr: &mut D, other: &Self) -> Result<Self> {
        let result = D::just(|| self.value.snag() & other.value.snag());
        let (a, b, c) = dr.mul(|| {
            let a = self.value.coeff().take();
            let b = other.value.coeff().take();
            let c = result.coeff().take();
            Ok((a, b, c))
        })?;

        dr.enforce_equal(&a, self.wire())?;
        dr.enforce_equal(&b, other.wire())?;

        Ok(Boolean {
            value: result,
            wire: c,
        })
    }

    /// Selects between two elements based on this boolean's value.
    /// Returns `a` when false, `b` when true.
    ///
    /// This costs one gate and two constraints.
    pub fn conditional_select(
        &self,
        dr: &mut D,
        a: &Element<'dr, D>,
        b: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        // Result = a + cond * (b - a)
        let diff = b.sub(dr, a);
        let cond_times_diff = self.element().mul(dr, &diff)?;
        Ok(a.add(dr, &cond_times_diff))
    }

    /// Conditionally enforces that two elements are equal.
    /// When this boolean is true, enforces `a == b`; when false, no constraint.
    ///
    /// This costs one gate and three constraints.
    pub fn conditional_enforce_equal(
        &self,
        dr: &mut D,
        a: &Element<'dr, D>,
        b: &Element<'dr, D>,
    ) -> Result<()> {
        // Enforce: condition → (a == b)
        // Equivalent to: condition * (a - b) == 0
        // - When condition = 1: a - b = 0
        // - When condition = 0: 0 = 0 (trivially satisfied)
        let diff = a.sub(dr, b);
        let product = self.element().mul(dr, &diff)?;
        product.enforce_zero(dr)
    }

    /// Returns the witness value of this boolean.
    pub fn value(&self) -> DriverValue<D, bool> {
        self.value.clone()
    }

    /// Returns the wire associated with this boolean.
    pub fn wire(&self) -> &D::Wire {
        &self.wire
    }

    /// Converts this boolean into an [`Element`].
    pub fn element(&self) -> Element<'dr, D> {
        Element::promote(self.wire.clone(), self.value().fe())
    }
}

/// Returns a boolean indicating whether the element is zero.
///
/// Uses the standard inverse trick for zero checking in arithmetic circuits.
pub(crate) fn is_zero<'dr, D: Driver<'dr>>(
    dr: &mut D,
    x: &Element<'dr, D>,
) -> Result<Boolean<'dr, D>> {
    // We enforce the constraints:
    //
    // - x * is_zero = 0
    // - x * inv = 1 - is_zero
    //
    // Given `x != 0`, the first constraint guarantees `is_zero = 0` as desired.
    // Given `x == 0`, the first constraint leaves `is_zero` unconstrained, but
    // the second constraint reduces to `0 = 1 - is_zero`, which reduces to
    // `is_zero = 1`, as desired. `inv` always has a solution, meaning it is
    // complete. By construction, `is_zero` is boolean constrained for all
    // satisfying assignments of these two constraints.

    let is_zero = x.value().map(|v| *v == D::F::ZERO);

    // Constraint 1: x * is_zero = 0.
    let (x_wire, is_zero_wire, zero_product) = dr.mul(|| {
        Ok((
            x.value().arbitrary().take(),
            is_zero.coeff().take(),
            Coeff::Zero,
        ))
    })?;
    dr.enforce_equal(&x_wire, x.wire())?;
    dr.enforce_zero(|lc| lc.add(&zero_product))?;

    // Constraint 2: x * inv = 1 - is_zero.
    let (x_wire, _, is_not_zero) = dr.mul(|| {
        Ok((
            x.value().arbitrary().take(),
            x.value()
                .map(|x| x.invert().unwrap_or(D::F::ZERO))
                .arbitrary()
                .take(),
            is_zero.not().coeff().take(),
        ))
    })?;
    dr.enforce_equal(&x_wire, x.wire())?;
    dr.enforce_zero(|lc| lc.add(&is_not_zero).sub(&D::ONE).add(&is_zero_wire))?;

    Ok(Boolean {
        wire: is_zero_wire,
        value: is_zero,
    })
}

impl<F: Field> Write<F> for Kind![F; @Boolean<'_, _>] {
    fn write_gadget<'dr, D: Driver<'dr, F = F>, B: Buffer<'dr, D>>(
        this: &Boolean<'dr, D>,
        dr: &mut D,
        buf: &mut B,
    ) -> Result<()> {
        this.element().write(dr, buf)
    }
}

impl<F: Field> Promotion<F> for Kind![F; @Boolean<'_, _>] {
    type Value = bool;

    fn promote<'dr, D: Driver<'dr, F = F>>(
        demoted: &Demoted<'dr, D, Boolean<'dr, D>>,
        witness: DriverValue<D, bool>,
    ) -> Boolean<'dr, D> {
        Boolean {
            wire: demoted.wire.clone(),
            value: witness,
        }
    }
}

/// Packs boolean slices into field elements using little-endian bit order.
///
/// The first bit in each chunk is the least significant bit.
pub fn multipack<'dr, D: Driver<'dr, F: ff::PrimeField>>(
    dr: &mut D,
    bits: &[Boolean<'dr, D>],
) -> Result<Vec<Element<'dr, D>>> {
    let capacity = D::F::CAPACITY as usize;
    let mut v = Vec::with_capacity(bits.len().div_ceil(capacity));
    for chunk in bits.chunks(capacity) {
        let value = D::just(|| {
            let mut value = D::F::ZERO;
            let mut gain = D::F::ONE;
            for bit in chunk.iter() {
                if bit.value().take() {
                    value += gain;
                }
                gain = gain.double();
            }
            value
        });

        let wire = dr.add(|mut lc| {
            for bit in chunk.iter() {
                lc = lc.add(bit.wire());
                lc = lc.gain(Coeff::Two);
            }
            lc
        });

        v.push(Element::promote(wire, value));
    }

    Ok(v)
}

impl<'dr, D: Driver<'dr>> Consistent<'dr, D> for Boolean<'dr, D> {
    fn enforce_consistent(&self, dr: &mut D) -> Result<()> {
        Self::alloc(dr, &mut (), self.value())?.enforce_equal(dr, self)
    }
}

/// A fixed-length boolean vector with single-constraint equality checking,
/// using a fixed-linear combination technique.
pub struct BooleanVec<'dr, D: Driver<'dr>, L: Len> {
    inner: FixedVec<Boolean<'dr, D>, L>,
}

impl<'dr, D: Driver<'dr>, L: Len> BooleanVec<'dr, D, L> {
    /// Creates a new `BooleanVec` from a `FixedVec` of booleans.
    pub fn new(inner: FixedVec<Boolean<'dr, D>, L>) -> Self {
        Self { inner }
    }

    /// Consumes this `BooleanVec` and returns the inner `FixedVec`.
    pub fn into_inner(self) -> FixedVec<Boolean<'dr, D>, L> {
        self.inner
    }

    /// Allocates a `BooleanVec` from witness values.
    pub fn alloc(dr: &mut D, values: FixedVec<DriverValue<D, bool>, L>) -> Result<Self> {
        let inner = values
            .into_iter()
            .map(|v| Boolean::alloc(dr, &mut (), v))
            .try_collect_fixed()?;
        Ok(Self { inner })
    }
}

impl<'dr, D: Driver<'dr>, L: Len> core::ops::Deref for BooleanVec<'dr, D, L> {
    type Target = [Boolean<'dr, D>];

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'dr, D: Driver<'dr>, L: Len> Clone for BooleanVec<'dr, D, L> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'dr, D: Driver<'dr>, L: Len> Gadget<'dr, D> for BooleanVec<'dr, D, L>
where
    D::F: PrimeField,
{
    type Kind = BooleanVecKind<L>;
}

/// The [`GadgetKind`] for [`BooleanVec`].
pub struct BooleanVecKind<L: Len> {
    _marker: PhantomData<L>,
}

// Safety: `BooleanVec` contains only `Boolean` gadgets which satisfy the `Send`
// requirement when `D::Wire` is `Send`.
unsafe impl<F: PrimeField, L: Len> GadgetKind<F> for BooleanVecKind<L> {
    type Rebind<'dr, D: Driver<'dr, F = F>> = BooleanVec<'dr, D, L>;

    fn map_gadget<'src, 'dst, WM: WireMap<F>>(
        this: &Bound<'src, WM::Src, Self>,
        wm: &mut WM,
    ) -> Result<Bound<'dst, WM::Dst, Self>>
    where
        WM::Src: Driver<'src, F = F>,
        WM::Dst: Driver<'dst, F = F>,
    {
        assert_eq!(this.inner.len(), L::len());
        let inner = this.inner.iter().map(|b| b.map(wm)).try_collect_fixed()?;
        Ok(BooleanVec { inner })
    }

    fn enforce_equal_gadget<
        'dr,
        D1: Driver<'dr, F = F>,
        D2: Driver<'dr, F = F, Wire = <D1 as Driver<'dr>>::Wire>,
    >(
        dr: &mut D1,
        a: &Bound<'dr, D2, Self>,
        b: &Bound<'dr, D2, Self>,
    ) -> Result<()> {
        // Chunk by F::CAPACITY to avoid field overflow, one constraint per chunk.
        let pairs: Vec<_> = a.iter().zip(b.iter()).collect();
        for chunk in pairs.chunks(F::CAPACITY as usize) {
            dr.enforce_zero(|mut lc| {
                for (a_bit, b_bit) in chunk {
                    lc = lc.add(a_bit.wire()).sub(b_bit.wire());
                    lc = lc.gain(Coeff::Two);
                }
                lc
            })?;
        }
        Ok(())
    }
}

impl<'dr, D: Driver<'dr>, L: Len> Consistent<'dr, D> for BooleanVec<'dr, D, L>
where
    D::F: PrimeField,
{
    fn enforce_consistent(&self, dr: &mut D) -> Result<()> {
        for b in self.iter() {
            b.enforce_consistent(dr)?;
        }
        Ok(())
    }
}

#[test]
fn test_boolean_alloc() -> Result<()> {
    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    let alloc = |bit: bool| {
        let sim = Simulator::simulate(bit, |dr, bit| {
            let allocated_bit = Boolean::alloc(dr, &mut (), bit.clone())?;

            assert_eq!(allocated_bit.value().take(), bit.clone().take());
            assert_eq!(*allocated_bit.wire(), bit.fe().take());

            Ok(())
        })?;
        assert_eq!(sim.num_gates(), 1);
        assert_eq!(sim.num_constraints(), 2);
        Ok(())
    };

    alloc(false)?;
    alloc(true)?;

    Ok(())
}

/// PoolAllocator reuses the Boolean gate's spare D wire for the Element.
#[test]
fn test_boolean_alloc_reclaim() -> Result<()> {
    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    let sim_without = Simulator::simulate(true, |dr, bit| {
        let _b = Boolean::alloc(dr, &mut (), bit)?;
        Element::alloc(dr, &mut (), Simulator::just(|| F::from(42u64)))?;
        Ok(())
    })?;
    let sim_with = Simulator::simulate(true, |dr, bit| {
        let allocator = &mut PoolAllocator::new();
        let _b = Boolean::alloc(dr, allocator, bit)?;
        Element::alloc(dr, allocator, Simulator::just(|| F::from(42u64)))?;
        Ok(())
    })?;

    assert_eq!(sim_without.num_gates(), 2);
    assert_eq!(sim_with.num_gates(), 1);

    Ok(())
}

/// Multiple Boolean donations pool up and serve later allocations.
#[test]
fn test_pool_allocator_multiple_donations() -> Result<()> {
    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    let sim = Simulator::simulate((true, false, true), |dr, witness| {
        let (b0, b1, b2) = witness.cast();
        let allocator = &mut PoolAllocator::new();

        let _b0 = Boolean::alloc(dr, allocator, b0)?;
        let _b1 = Boolean::alloc(dr, allocator, b1)?;
        let _b2 = Boolean::alloc(dr, allocator, b2)?;

        let _e0 = Element::alloc(dr, allocator, Simulator::just(|| F::from(1u64)))?;
        let _e1 = Element::alloc(dr, allocator, Simulator::just(|| F::from(2u64)))?;
        let _e2 = Element::alloc(dr, allocator, Simulator::just(|| F::from(3u64)))?;

        Ok(())
    })?;

    assert_eq!(sim.num_gates(), 3);

    Ok(())
}

#[test]
fn test_conditional_select() -> Result<()> {
    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    // condition = true (returns b)
    Simulator::simulate((true, F::from(1u64), F::from(2u64)), |dr, witness| {
        let (cond, a, b) = witness.cast();
        let allocator = &mut SimpleAllocator::new();
        let cond = Boolean::alloc(dr, &mut (), cond)?;
        let a = Element::alloc(dr, allocator, a)?;
        let b = Element::alloc(dr, allocator, b)?;

        let result = cond.conditional_select(dr, &a, &b)?;
        assert_eq!(*result.value().take(), F::from(2u64));

        Ok(())
    })?;

    // condition = false (returns a)
    Simulator::simulate((false, F::from(1u64), F::from(2u64)), |dr, witness| {
        let (cond, a, b) = witness.cast();
        let allocator = &mut SimpleAllocator::new();
        let cond = Boolean::alloc(dr, &mut (), cond)?;
        let a = Element::alloc(dr, allocator, a)?;
        let b = Element::alloc(dr, allocator, b)?;

        let result = cond.conditional_select(dr, &a, &b)?;
        assert_eq!(*result.value().take(), F::from(1u64));

        Ok(())
    })?;

    Ok(())
}

#[test]
fn test_conditional_enforce_equal() -> Result<()> {
    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    // When condition is true, a == b should be enforced (and satisfied)
    let sim = Simulator::simulate((true, F::from(42u64), F::from(42u64)), |dr, witness| {
        let (cond, a, b) = witness.cast();
        let allocator = &mut SimpleAllocator::new();
        let cond = Boolean::alloc(dr, &mut (), cond)?;
        let a = Element::alloc(dr, allocator, a)?;
        let b = Element::alloc(dr, allocator, b)?;

        dr.reset();
        cond.conditional_enforce_equal(dr, &a, &b)?;
        Ok(())
    })?;

    assert_eq!(sim.num_gates(), 1);
    assert_eq!(sim.num_constraints(), 3);

    // When condition is false, constraint is trivially satisfied even if a != b
    Simulator::simulate((false, F::from(1u64), F::from(2u64)), |dr, witness| {
        let (cond, a, b) = witness.cast();
        let allocator = &mut SimpleAllocator::new();
        let cond = Boolean::alloc(dr, &mut (), cond)?;
        let a = Element::alloc(dr, allocator, a)?;
        let b = Element::alloc(dr, allocator, b)?;

        cond.conditional_enforce_equal(dr, &a, &b)?;
        Ok(())
    })?;

    Ok(())
}

#[test]
fn test_multipack() -> Result<()> {
    use alloc::vec::Vec;

    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    let bits = (0..1000).map(|i| i % 2 == 0).collect::<Vec<_>>();

    Simulator::simulate(bits, |dr, bits| {
        let bits = (0..1000)
            .map(|i| Boolean::alloc(dr, &mut (), bits.as_ref().map(|b| b[i])))
            .collect::<Result<Vec<_>>>()?;

        let vals = multipack(dr, &bits)?;
        assert_eq!(vals.len(), 4);

        for val in vals {
            assert_eq!(val.value().take(), val.wire());
        }

        Ok(())
    })?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use ragu_core::maybe::Maybe;

    use super::*;

    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    #[test]
    fn test_is_equal_same() -> Result<()> {
        let sim = Simulator::simulate((F::from(123u64), F::from(123u64)), |dr, witness| {
            let (a_val, b_val) = witness.cast();
            let allocator = &mut SimpleAllocator::new();
            let a = Element::alloc(dr, allocator, a_val)?;
            let b = Element::alloc(dr, allocator, b_val)?;

            dr.reset();
            let eq = a.is_equal(dr, &b)?;

            assert!(eq.value().take(), "Expected a == b");
            Ok(())
        })?;

        assert_eq!(sim.num_gates(), 2);
        assert_eq!(sim.num_constraints(), 4);

        Ok(())
    }

    #[test]
    fn test_is_not_equal() -> Result<()> {
        Simulator::simulate((F::from(1u64), F::from(123u64)), |dr, witness| {
            let (a_val, b_val) = witness.cast();
            let allocator = &mut SimpleAllocator::new();
            let a = Element::alloc(dr, allocator, a_val)?;
            let b = Element::alloc(dr, allocator, b_val)?;

            dr.reset();
            let eq = a.is_equal(dr, &b)?;

            assert!(!eq.value().take(), "Expected a != b");
            Ok(())
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod proptests {
    use alloc::format;

    use proptest::prelude::*;
    use ragu_core::maybe::Maybe;

    use super::*;

    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    fn arb_fe() -> impl Strategy<Value = F> {
        (any::<u64>(), any::<u64>())
            .prop_map(|(a, b)| F::from(a) + F::from(b) * F::MULTIPLICATIVE_GENERATOR)
    }

    proptest! {
        #[test]
        fn boolean_and_idempotent(a_val in proptest::bool::ANY) {
            let mut actual = None;
            Simulator::simulate(a_val, |dr, witness| {
                let a = Boolean::alloc(dr, &mut (), witness)?;
                let result = a.and(dr, &a)?;
                actual = Some(result.value().take());
                Ok(())
            }).map_err(|e| TestCaseError::fail(format!("{e:?}")))?;
            prop_assert_eq!(actual, Some(a_val));
        }

        #[test]
        fn boolean_and_complement(a_val in proptest::bool::ANY) {
            let mut actual = None;
            Simulator::simulate(a_val, |dr, witness| {
                let a = Boolean::alloc(dr, &mut (), witness)?;
                let not_a = a.not(dr);
                let result = a.and(dr, &not_a)?;
                actual = Some(result.value().take());
                Ok(())
            }).map_err(|e| TestCaseError::fail(format!("{e:?}")))?;
            prop_assert_eq!(actual, Some(false));
        }

        #[test]
        fn conditional_select_correctness(
            cond in proptest::bool::ANY,
            a_fe in arb_fe(),
            b_fe in arb_fe(),
        ) {
            let expected = if cond { b_fe } else { a_fe };
            let mut actual = None;
            Simulator::simulate((cond, a_fe, b_fe), |dr, witness| {
                let (c, a, b) = witness.cast();
                let allocator = &mut SimpleAllocator::new();
                let c = Boolean::alloc(dr, &mut (), c)?;
                let a = Element::alloc(dr, allocator, a)?;
                let b = Element::alloc(dr, allocator, b)?;
                let result = c.conditional_select(dr, &a, &b)?;
                actual = Some(*result.value().take());
                Ok(())
            }).map_err(|e| TestCaseError::fail(format!("{e:?}")))?;
            prop_assert_eq!(actual, Some(expected));
        }
    }
}

#[test]
fn test_multipack_vector() -> Result<()> {
    use alloc::{vec, vec::Vec};

    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    let bits = vec![false, true, true, false, true]; // 0b10110 = 22
    Simulator::simulate(bits, |dr, bits| {
        let bits = (0..5)
            .map(|i| Boolean::alloc(dr, &mut (), bits.as_ref().map(|b| b[i])))
            .collect::<Result<Vec<_>>>()?;

        let vals = multipack(dr, &bits)?;
        assert_eq!(vals.len(), 1);
        assert_eq!(*vals[0].value().take(), F::from(22));
        assert_eq!(*vals[0].wire(), F::from(22));

        Ok(())
    })?;

    Ok(())
}

#[test]
fn test_boolean_vec_equality() -> Result<()> {
    use alloc::vec;

    use ragu_core::gadgets::Gadget;

    use crate::vec::ConstLen;
    type F = ragu_pasta::Fp;
    type Simulator = crate::Simulator<F>;

    let bits = vec![true, false, true, true, false, false, true, true];
    let sim = Simulator::simulate((bits.clone(), bits), |dr, witness| {
        let (a_bits, b_bits) = witness.cast();
        let a: BooleanVec<_, ConstLen<8>> = BooleanVec::new(
            (0..8)
                .map(|i| Boolean::alloc(dr, &mut (), a_bits.as_ref().map(|b| b[i])))
                .try_collect_fixed()?,
        );
        let b: BooleanVec<_, ConstLen<8>> = BooleanVec::new(
            (0..8)
                .map(|i| Boolean::alloc(dr, &mut (), b_bits.as_ref().map(|b| b[i])))
                .try_collect_fixed()?,
        );
        dr.reset();
        a.enforce_equal(dr, &b)?;

        Ok(())
    })?;

    assert_eq!(sim.num_constraints(), 1);

    Ok(())
}
