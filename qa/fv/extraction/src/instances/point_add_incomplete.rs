use group::CurveAffine;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::{NonzeroBank, Point};

use crate::instance::{CircuitInstance, InstanceDriver, WireCollector, WireDeserializer};

pub struct PointAddIncompleteInstance;

impl CircuitInstance for PointAddIncompleteInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        let input_wires_1 = dr.alloc_input_wires(2);
        let input_wires_2 = dr.alloc_input_wires(2);

        // Reuse a constant point as a structural template, then substitute the
        // raw input wires into its `[x, y]` gadget fields.
        let point_template = Point::constant(dr, EpAffine::generator())?;
        let p1 = WireDeserializer::new(input_wires_1).into_gadget(&point_template)?;
        let p2 = WireDeserializer::new(input_wires_2).into_gadget(&point_template)?;

        // `NonzeroBank::scope` discharges `x2 ≠ x1` in-circuit, so the trace is
        // self-contained: callers don't need to feed a running-product wire.
        let p3 = NonzeroBank::scope(dr, |dr, bank| p1.add_incomplete(dr, &p2, bank))?;

        WireCollector::collect_from(&p3)
    }
}
