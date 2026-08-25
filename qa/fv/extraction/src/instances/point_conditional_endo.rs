use group::CurveAffine;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::Point;

use crate::{
    instance::{CircuitInstance, FvDriver, WireCollector, WireDeserializer},
    wire_remap::boolean_from_wire,
};

pub struct PointConditionalEndoInstance;

impl CircuitInstance for PointConditionalEndoInstance {
    type Field = Fp;

    /// Drives the real `Point::conditional_endo` with the condition input wire
    /// wrapped as a `Boolean` (see [`boolean_from_wire`]).
    ///
    /// Input wires: `cond`, then the point's `(x, y)`. Output: the resulting
    /// point's `(x, y)`.
    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        let cond_wires = dr.alloc_input_wires(1);
        let point_wires = dr.alloc_input_wires(2);

        let cond = boolean_from_wire(cond_wires[0].clone())?;
        let point_template = Point::constant(dr, EpAffine::generator())?;
        let point = WireDeserializer::new(point_wires).into_gadget(&point_template)?;

        let result = point.conditional_endo(dr, &cond)?;

        WireCollector::collect_from(&result)
    }
}
