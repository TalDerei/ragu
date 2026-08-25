use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, InstanceDriver, WireCollector, WireDeserializer};

pub struct ElementFoldInstanceN2;

impl CircuitInstance for ElementFoldInstanceN2 {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        // n = 2: exactly one Mul gate — the last of the Lean reimpl's small-n
        // branches before the uniform `n >= 3` case that N3/N7/N19 pin.
        fold_at_length::<D, 2>(dr)
    }
}

pub struct ElementFoldInstanceN3;

impl CircuitInstance for ElementFoldInstanceN3 {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        // n = 3: smallest non-trivial Horner shape (one element gives a no-op,
        // two elements is one Mul). The polymorphic Lean reimpl is universal
        // in `n`; this instance pins it to n=3 for byte-equality against the
        // extracted trace. See N7/N19 for production-shape instances.
        fold_at_length::<D, 3>(dr)
    }
}

pub struct ElementFoldInstanceN7;

impl CircuitInstance for ElementFoldInstanceN7 {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        // n = 7: matches `RevdotParameters::GroupSize` in
        // `crates/ragu_pcd/src/internal/native/mod.rs`. This is the inner-fold
        // length used by `fold_revdot.rs::fold_two_layer` for each chunk of
        // group sources.
        fold_at_length::<D, 7>(dr)
    }
}

pub struct ElementFoldInstanceN19;

impl CircuitInstance for ElementFoldInstanceN19 {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        // n = 19: matches `RevdotParameters::NumGroups` in
        // `crates/ragu_pcd/src/internal/native/mod.rs`. This is the outer-fold
        // length `fold_revdot.rs::fold_two_layer` uses over the group results.
        fold_at_length::<D, 19>(dr)
    }
}

fn fold_at_length<'dr, D: InstanceDriver<'dr, F = Fp>, const N: usize>(
    dr: &mut D,
) -> ragu_core::Result<Vec<D::Wire>> {
    let element_template = Element::constant(dr, Fp::zero());

    let mut xs = Vec::with_capacity(N);
    for _ in 0..N {
        let input_wires = dr.alloc_input_wires(1);
        let x = WireDeserializer::new(input_wires).into_gadget(&element_template)?;
        xs.push(x);
    }
    let scale_wires = dr.alloc_input_wires(1);
    let scale = WireDeserializer::new(scale_wires).into_gadget(&element_template)?;

    let result = Element::fold(dr, xs.iter(), &scale)?;

    WireCollector::collect_from(&result)
}
