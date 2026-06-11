use ff::{Field, WithSmallOrderMulGroup};
use group::CurveAffine;
use ragu_arithmetic::Coeff;
use ragu_core::drivers::{Driver, LinearExpression};
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::{Element, NonzeroBank, Point};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct EndoscalarGroupScaleInstance;

impl CircuitInstance for EndoscalarGroupScaleInstance {
    type Field = Fp;

    /// Mirrors `Endoscalar::group_scale` on the constraint side without going
    /// through `Endoscalar` (whose fields are private) or `Boolean::alloc`
    /// (which would allocate fresh wires for each input bit).
    ///
    /// Input wires (in order):
    ///   * bits[0..128]   (128 wires) — the 128 boolean bits of the endoscalar
    ///   * p.x, p.y       (2 wires)   — the curve point being scaled
    ///
    /// Output: a single `Point` (x, y) — the scaled point.
    ///
    /// **Unchecked bank, mirroring the deployed gadget**: `group_scale`
    /// creates its bank with `NonzeroBank::new_unchecked()`, so no fold or
    /// discharge constraints are emitted — the distinct-x conditions of every
    /// `add_incomplete` / `double_and_add_incomplete` rest on the Appendix C
    /// no-collision argument (BGH19), not on the constraint system. This
    /// instance does the same, so the trace digest matches the circuit that
    /// actually ships. The Lean side carries the corresponding non-degeneracy
    /// as an explicit `Assumptions` conjunct (`groupScaleNative ≠ none`).
    ///
    /// **Freshening hack** (still required): `double_and_add_incomplete`'s
    /// output `x_s, y_s` are symbolic Expr trees in which the input `x1, y1`
    /// appear multiple times. Chaining 64 of these explodes the tree. We
    /// `Element::mul`-by-one each output coordinate after every DAA,
    /// materializing a fresh `Expr::Var(N)` at each iteration boundary.
    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // Allocate 128 input wires for the bits.
        let bit_wires: Vec<Expr<Fp>> = (0..128usize)
            .map(|_| dr.alloc_input_wires(1).into_iter().next().unwrap())
            .collect();
        // Allocate 2 input wires for the curve point p.
        let point_input_wires = dr.alloc_input_wires(2);
        let point_template = Point::constant(dr, EpAffine::generator())?;
        let p = WireDeserializer::new(point_input_wires).into_gadget(&point_template)?;

        // Extract p's x and y wires as Expr for inline reuse.
        let p_wires = WireCollector::collect_from(&p)?;
        let p_x_wire = p_wires[0].clone();
        let p_y_wire = p_wires[1].clone();
        let p_x = Element::promote(p_x_wire.clone(), ExtractionDriver::<Fp>::just(|| Fp::ZERO));
        let p_y = Element::promote(p_y_wire.clone(), ExtractionDriver::<Fp>::just(|| Fp::ZERO));

        let one_elem = Element::constant(dr, Fp::ONE);

        // Init step: p_endo = (ζ·p.x, p.y).
        let p_endo = {
            let endo_x = p_x.scale(dr, Coeff::Arbitrary(Fp::ZETA));
            let endo_x_wire = WireCollector::collect_from(&endo_x)?[0].clone();
            let wires = vec![endo_x_wire, p_y_wire.clone()];
            WireDeserializer::new(wires).into_gadget(&point_template)?
        };

        // One unchecked bank for the whole gadget, exactly as the deployed
        // `Endoscalar::group_scale` does: folds and the drop are no-ops.
        let mut bank = NonzeroBank::new_unchecked();

        let acc_pre = p_endo.add_incomplete(dr, &p, &mut bank)?;
        let mut acc = acc_pre.double(dr)?;

        for i in 0..64usize {
            let n_wire = &bit_wires[2 * i];
            let e_wire = &bit_wires[2 * i + 1];

            // Inline ConditionalNegate (Boolean.ConditionalSelect on y / -y).
            let neg_y = p_y.scale(dr, Coeff::Arbitrary(-Fp::ONE));
            let diff_y = neg_y.sub(dr, &p_y);
            let (mul_a_n, mul_b_n, mul_c_n) =
                dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
            dr.enforce_equal(&mul_a_n, n_wire)?;
            let diff_y_wire = WireCollector::collect_from(&diff_y)?[0].clone();
            dr.enforce_equal(&mul_b_n, &diff_y_wire)?;
            let s_y_wire = dr.add(|lc| lc.add(&p_y_wire).add(&mul_c_n));

            // Inline ConditionalEndo (Boolean.ConditionalSelect on x / ζ·x).
            let endo_x = p_x.scale(dr, Coeff::Arbitrary(Fp::ZETA));
            let diff_x = endo_x.sub(dr, &p_x);
            let (mul_a_e, mul_b_e, mul_c_e) =
                dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
            dr.enforce_equal(&mul_a_e, e_wire)?;
            let diff_x_wire = WireCollector::collect_from(&diff_x)?[0].clone();
            dr.enforce_equal(&mul_b_e, &diff_x_wire)?;
            let s_x_wire = dr.add(|lc| lc.add(&p_x_wire).add(&mul_c_e));

            let s_wires = vec![s_x_wire, s_y_wire];
            let s: Point<'_, _, EpAffine> =
                WireDeserializer::new(s_wires).into_gadget(&point_template)?;

            // acc' = acc.double_and_add_incomplete(s) against the unchecked bank.
            let acc_sym = acc.double_and_add_incomplete(dr, &s, &mut bank)?;

            // Freshen acc'.x and acc'.y by multiplying each by 1.
            let acc_sym_wires = WireCollector::collect_from(&acc_sym)?;
            let acc_sym_x = Element::promote(
                acc_sym_wires[0].clone(),
                ExtractionDriver::<Fp>::just(|| Fp::ZERO),
            );
            let acc_sym_y = Element::promote(
                acc_sym_wires[1].clone(),
                ExtractionDriver::<Fp>::just(|| Fp::ZERO),
            );
            let fresh_x = acc_sym_x.mul(dr, &one_elem)?;
            let fresh_y = acc_sym_y.mul(dr, &one_elem)?;
            let fresh_x_wire = WireCollector::collect_from(&fresh_x)?[0].clone();
            let fresh_y_wire = WireCollector::collect_from(&fresh_y)?[0].clone();
            let fresh_wires = vec![fresh_x_wire, fresh_y_wire];
            acc = WireDeserializer::new(fresh_wires).into_gadget(&point_template)?;
        }

        WireCollector::collect_from(&acc)
    }
}
