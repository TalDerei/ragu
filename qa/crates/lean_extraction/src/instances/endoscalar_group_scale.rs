use group::CurveAffine;
use ragu_core::drivers::Driver;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::{Point, fv_utils};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer, boolean_from_wire},
};

pub struct EndoscalarGroupScaleInstance;

impl CircuitInstance for EndoscalarGroupScaleInstance {
    type Field = Fp;

    /// Drives the real `Endoscalar::group_scale` on an `Endoscalar` assembled
    /// from the bit input wires (see [`boolean_from_wire`] and
    /// `fv_utils::endoscalar_unchecked`) and a point assembled from the
    /// coordinate input wires. The gadget builds its own unchecked
    /// `NonzeroBank`, so — as in the deployed circuit — no fold or discharge
    /// constraints are emitted; the Lean reimplementation carries that
    /// non-degeneracy as an explicit `Assumptions` conjunct.
    ///
    /// Input wires (in order): `bits[0..128]` (least significant first), then
    /// the point's `(x, y)`. Output: the scaled point's `(x, y)`.
    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let bits: Vec<_> = dr
            .alloc_input_wires(128)
            .into_iter()
            .map(boolean_from_wire)
            .collect::<ragu_core::Result<_>>()?;
        let point_wires = dr.alloc_input_wires(2);

        let endo = fv_utils::endoscalar_unchecked(&bits, ExtractionDriver::<Fp>::just(|| 0u128))?;
        let point_template = Point::constant(dr, EpAffine::generator())?;
        let p = WireDeserializer::new(point_wires).into_gadget(&point_template)?;

        let acc = endo.group_scale(dr, &p)?;

        WireCollector::collect_from(&acc)
    }
}
