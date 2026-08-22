use group::CurveAffine;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::Point;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer, boolean_from_wire},
};

pub struct PointConditionalNegateInstance;

impl CircuitInstance for PointConditionalNegateInstance {
    type Field = Fp;

    /// Drives the real `Point::conditional_negate` with the condition input
    /// wire wrapped as a `Boolean` (see [`boolean_from_wire`]).
    ///
    /// Input wires: `cond`, then the point's `(x, y)`. Output: the resulting
    /// point's `(x, y)`.
    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let point_wires = dr.alloc_input_wires(2);

        let cond = boolean_from_wire(cond_wires[0].clone())?;
        let point_template = Point::constant(dr, EpAffine::generator())?;
        let point = WireDeserializer::new(point_wires).into_gadget(&point_template)?;

        let result = point.conditional_negate(dr, &cond)?;

        WireCollector::collect_from(&result)
    }
}
