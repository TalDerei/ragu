use group::CurveAffine;
use ragu_pasta::{EpAffine, EqAffine, Fp, Fq};
use ragu_primitives::{Point, consistent::Consistent};

use crate::instance::{CircuitInstance, FvDriver, WireDeserializer};

/// `Point::enforce_consistent` on a point assembled from two input wires: a
/// fresh `Point::alloc` — the on-curve check — seeded from the point's own
/// coordinates, linked to it coordinate by coordinate. This is what the
/// staging machinery re-emits when it substitutes a point's wires into a
/// context where `alloc` never ran.
///
/// Input wires: `x, y` (2 wires). No outputs.
pub struct PointConsistentInstanceFp;

impl CircuitInstance for PointConsistentInstanceFp {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        let point_wires = dr.alloc_input_wires(2);
        let point_template = Point::constant(dr, EpAffine::generator())?;
        let point = WireDeserializer::new(point_wires).into_gadget(&point_template)?;

        point.enforce_consistent(dr)?;

        Ok(Vec::new())
    }
}

/// As [`PointConsistentInstanceFp`] on the other curve of the cycle.
pub struct PointConsistentInstanceFq;

impl CircuitInstance for PointConsistentInstanceFq {
    type Field = Fq;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fq>,
    {
        let point_wires = dr.alloc_input_wires(2);
        let point_template = Point::constant(dr, EqAffine::generator())?;
        let point = WireDeserializer::new(point_wires).into_gadget(&point_template)?;

        point.enforce_consistent(dr)?;

        Ok(Vec::new())
    }
}
