use group::CurveAffine;
use ragu_pasta::{EpAffine, EqAffine, Fp, Fq};
use ragu_primitives::Point;

use crate::instance::{CircuitInstance, FvDriver, WireCollector};

pub struct PointAllocInstanceFp;

impl CircuitInstance for PointAllocInstanceFp {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        // MaybeKind = Empty: the closure is never called.
        let assignment = D::just(EpAffine::identity);
        let point = Point::<_, EpAffine>::alloc(dr, assignment)?;

        // NOTE: assumes that the serialization is [x, y].
        // TODO: This is an assumption we should not make in general, and would be better if we "manually"
        // serialize the output into a Vector. However, Point wires are private, so this is the only way
        // for now
        WireCollector::collect_from(&point)
    }
}

pub struct PointAllocInstanceFq;

impl CircuitInstance for PointAllocInstanceFq {
    type Field = Fq;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fq>,
    {
        // MaybeKind = Empty: the closure is never called.
        let assignment = D::just(EqAffine::identity);
        let point = Point::<_, EqAffine>::alloc(dr, assignment)?;

        // NOTE: assumes that the serialization is [x, y].
        // TODO: This is an assumption we should not make in general, and would be better if we "manually"
        // serialize the output into a Vector. However, Point wires are private, so this is the only way
        // for now
        WireCollector::collect_from(&point)
    }
}
