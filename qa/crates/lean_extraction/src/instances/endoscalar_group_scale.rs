use ff::Field;
use group::CurveAffine;
use ragu_arithmetic::Coeff;
use ragu_core::drivers::Driver;
use ragu_pasta::{EpAffine, Fp};
use ragu_primitives::{Element, Point};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer, boolean_from_wire},
};

type Dr = ExtractionDriver<Fp>;

/// Mirrors `Element::divide`'s constraint sequence.
///
/// `Element::divide` takes a `&Nonzero` divisor, and `Nonzero` has no public
/// constructor: outside `ragu_primitives` the only source of one is a
/// `NonzeroBank`, and the unchecked constructor `Endoscalar::group_scale` uses
/// is `pub(crate)`. In unchecked mode that bank is the identity — `fold`
/// returns `Nonzero::new_unchecked(elem)` and emits nothing, and the discharge
/// is a no-op — so reproducing the division here is exact, not an
/// approximation.
///
/// Op-for-op identical to `Element::divide`: one `mul` gate, then the numerator
/// bound to the gate's `c` wire, then the divisor bound to `b`. `enforce_equal`
/// emits `Assert(a - b)`, so the argument order is part of the trace.
fn divide<'dr>(
    dr: &mut Dr,
    numerator: &Element<'dr, Dr>,
    divisor: &Element<'dr, Dr>,
) -> ragu_core::Result<Element<'dr, Dr>> {
    let (quotient, denominator, numerator_wire) =
        dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
    dr.enforce_equal(numerator.wire(), &numerator_wire)?;
    dr.enforce_equal(divisor.wire(), &denominator)?;

    Ok(Element::promote(quotient, Dr::just(|| Fp::ZERO)))
}

/// Splits a point into its `(x, y)` coordinate elements. Emits nothing.
fn coords<'dr>(
    p: &Point<'dr, Dr, EpAffine>,
) -> ragu_core::Result<(Element<'dr, Dr>, Element<'dr, Dr>)> {
    let wires = WireCollector::collect_from(p)?;
    Ok((
        Element::promote(wires[0].clone(), Dr::just(|| Fp::ZERO)),
        Element::promote(wires[1].clone(), Dr::just(|| Fp::ZERO)),
    ))
}

/// Reassembles a point from coordinate elements, using `template` for the
/// gadget structure. Emits nothing.
fn point_from<'dr>(
    template: &Point<'dr, Dr, EpAffine>,
    x: &Element<'dr, Dr>,
    y: &Element<'dr, Dr>,
) -> ragu_core::Result<Point<'dr, Dr, EpAffine>> {
    WireDeserializer::new(vec![x.wire().clone(), y.wire().clone()]).into_gadget(template)
}

/// Mirrors `Point::add_incomplete` driven by an unchecked bank.
///
/// The two differ only in the bank, which is the identity in unchecked mode, so
/// dropping it leaves the emitted trace unchanged. Body and comments track
/// `crates/ragu_primitives/src/point.rs` line for line.
fn add_incomplete_unchecked<'dr>(
    dr: &mut Dr,
    p: &Point<'dr, Dr, EpAffine>,
    other: &Point<'dr, Dr, EpAffine>,
    template: &Point<'dr, Dr, EpAffine>,
) -> ragu_core::Result<Point<'dr, Dr, EpAffine>> {
    let (x0, y0) = coords(p)?;
    let (x1, y1) = coords(other)?;

    // delta = (y1 - y0) / (x1 - x0)
    let tmp = x1.sub(dr, &x0);
    let numerator = y1.sub(dr, &y0);
    let delta = divide(dr, &numerator, &tmp)?;

    // x3 = delta^2 - x0 - x1
    let x3 = delta.square(dr)?.sub(dr, &x0).sub(dr, &x1);

    // y3 = delta * (x0 - x3) - y0
    let tmp = x0.sub(dr, &x3);
    let y3 = delta.mul(dr, &tmp)?.sub(dr, &y0);

    point_from(template, &x3, &y3)
}

/// Mirrors `Point::double_and_add_incomplete` driven by an unchecked bank.
///
/// See [`add_incomplete_unchecked`] for why dropping the bank is trace-neutral.
/// Body and comments track `crates/ragu_primitives/src/point.rs` line for line.
fn double_and_add_incomplete_unchecked<'dr>(
    dr: &mut Dr,
    p: &Point<'dr, Dr, EpAffine>,
    other: &Point<'dr, Dr, EpAffine>,
    template: &Point<'dr, Dr, EpAffine>,
) -> ragu_core::Result<Point<'dr, Dr, EpAffine>> {
    let (x_p, y_p) = coords(p)?;
    let (x_q, y_q) = coords(other)?;

    // lambda_1 = (y_q - y_p)/(x_q - x_p)
    let tmp = x_q.sub(dr, &x_p);
    let numerator = y_q.sub(dr, &y_p);
    let lambda_1 = divide(dr, &numerator, &tmp)?;

    // x_r = lambda_1^2 - x_p - x_q
    let x_r = lambda_1.square(dr)?.sub(dr, &x_p).sub(dr, &x_q);

    // lambda_2 = 2 y_p /(x_p - x_r) - lambda_1
    let tmp = x_p.sub(dr, &x_r);
    let numerator = y_p.double(dr);
    let lambda_2 = divide(dr, &numerator, &tmp)?.sub(dr, &lambda_1);

    // x_s = lambda_2^2 - x_r - x_p
    let x_s = lambda_2.square(dr)?.sub(dr, &x_r).sub(dr, &x_p);

    // y_s = lambda_2 (x_p - x_s) - y_p
    let tmp = x_p.sub(dr, &x_s);
    let y_s = lambda_2.mul(dr, &tmp)?.sub(dr, &y_p);

    point_from(template, &x_s, &y_s)
}

pub struct EndoscalarGroupScaleInstance;

impl CircuitInstance for EndoscalarGroupScaleInstance {
    type Field = Fp;

    /// Mirrors `Endoscalar::group_scale` on the constraint side. The bit wires
    /// are wrapped as `Boolean`s (see [`boolean_from_wire`]) and the per-step
    /// `conditional_negate` / `conditional_endo` are the real `Point` methods;
    /// only the incomplete additions and their `divide` are mirrored. An
    /// `Endoscalar` could be assembled from the input wires the same way (an
    /// `unstable-fv` constructor, like `Boolean::new_unchecked`), but driving
    /// the real `group_scale` would record the accumulator as an exponentially
    /// large tree — see the freshening note below — so the loop body is
    /// mirrored instead.
    ///
    /// Input wires (in order):
    ///   * bits[0..128]   (128 wires) — the 128 boolean bits of the endoscalar
    ///   * p.x, p.y       (2 wires)   — the curve point being scaled
    ///
    /// Output: a single `Point` (x, y) — the scaled point.
    ///
    /// **Unchecked bank, mirroring the deployed gadget**: `group_scale` creates
    /// its bank with `NonzeroBank::new_unchecked()`, so no fold or discharge
    /// constraints are emitted — the distinct-x conditions of every
    /// `add_incomplete` / `double_and_add_incomplete` rest on the Appendix C
    /// no-collision argument (BGH19), not on the constraint system. That
    /// constructor is `pub(crate)`, so rather than widen `ragu_primitives` this
    /// instance uses the [`add_incomplete_unchecked`] /
    /// [`double_and_add_incomplete_unchecked`] mirrors above, which emit the
    /// same trace with no bank at all. The Lean side carries the corresponding
    /// non-degeneracy as an explicit `Assumptions` conjunct
    /// (`groupScaleNative ≠ none`).
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

        let one_elem = Element::constant(dr, Fp::ONE);

        // Init step, as in `group_scale`: `p.endo()` is the real `Point` method.
        let p_endo = p.endo(dr);

        let acc_pre = add_incomplete_unchecked(dr, &p_endo, &p, &point_template)?;
        let mut acc = acc_pre.double(dr)?;

        for i in 0..64usize {
            // As in `group_scale`: negate on the first bit of the pair, then endo
            // on the second, both the real `Point` methods.
            let negate_bit = boolean_from_wire(bit_wires[2 * i].clone());
            let endo_bit = boolean_from_wire(bit_wires[2 * i + 1].clone());
            let s = p
                .conditional_negate(dr, &negate_bit)?
                .conditional_endo(dr, &endo_bit)?;

            // acc' = acc.double_and_add_incomplete(s) with the unchecked bank.
            let acc_sym = double_and_add_incomplete_unchecked(dr, &acc, &s, &point_template)?;

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
