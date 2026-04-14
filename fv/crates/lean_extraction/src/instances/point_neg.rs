use group::prime::PrimeCurveAffine;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::Point;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct PointNegInstance;

impl CircuitInstance for PointNegInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires = dr.alloc_input_wires(2);

        // Reuse a constant point as a structural template, then substitute the
        // raw input wires into its `[x, y]` gadget fields.
        let template = Point::constant(dr, EpAffine::generator())?;
        let input_point = WireDeserializer::new(input_wires).into_gadget(&template)?;

        let point_neg = input_point.negate(dr);

        WireCollector::collect_from(&point_neg)
    }
}
