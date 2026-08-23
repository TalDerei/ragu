use ff::Field;
use ragu_core::drivers::Driver;
use ragu_pasta::{EpAffine, EqAffine, Fp, Fq};
use ragu_primitives::Point;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct PointAllocInstanceFp;

impl CircuitInstance for PointAllocInstanceFp {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // MaybeKind = Empty: the closure is never called.
        let assignment = ExtractionDriver::<Fp>::just(|| Fp::ZERO);
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

    fn circuit(dr: &mut ExtractionDriver<Fq>) -> ragu_core::Result<Vec<Expr<Fq>>> {
        // MaybeKind = Empty: the closure is never called.
        let assignment = ExtractionDriver::<Fq>::just(|| Fq::ZERO);
        let point = Point::<_, EqAffine>::alloc(dr, assignment)?;

        // NOTE: assumes that the serialization is [x, y].
        // TODO: This is an assumption we should not make in general, and would be better if we "manually"
        // serialize the output into a Vector. However, Point wires are private, so this is the only way
        // for now
        WireCollector::collect_from(&point)
    }
}
