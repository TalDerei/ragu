use ragu_pasta::Fp;
use ragu_primitives::consistent::Consistent;

use crate::{
    instance::{CircuitInstance, InstanceDriver},
    wire_remap::boolean_from_wire,
};

/// `Boolean::enforce_consistent` on a boolean assembled from one input wire:
/// a fresh `Boolean::alloc` seeded from the wire's own value, linked to it by
/// one equality. This is the constraint the staging machinery re-emits when
/// it substitutes a boolean's wire into a context where `alloc` never ran.
///
/// Input wire: the boolean (1 wire). No outputs.
pub struct BooleanConsistentInstance;

impl CircuitInstance for BooleanConsistentInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        let wire = dr
            .alloc_input_wires(1)
            .into_iter()
            .next()
            .expect("one input wire");
        let boolean = boolean_from_wire(wire)?;

        boolean.enforce_consistent(dr)?;

        Ok(Vec::new())
    }
}
