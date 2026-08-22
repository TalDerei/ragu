use ff::{Field, WithSmallOrderMulGroup};
use ragu_arithmetic::Coeff;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct EndoscalarLiftInstance;

impl CircuitInstance for EndoscalarLiftInstance {
    type Field = Fp;

    /// Mirrors `Endoscalar::lift` on the constraint side without going through
    /// `Endoscalar` (whose fields are private). For each of the 64 bit pairs
    /// `(n, e)` the `Boolean::and(n, e)` body is inlined — one `mul` gate plus
    /// two `enforce_equal`s, the same pattern as `boolean_and.rs`, because
    /// `Boolean` has no constructor from a bare wire. Everything else is the
    /// deployed gadget's own `Element` calls (`zero`, `scale`, `add`,
    /// `constant`), in the deployed order.
    ///
    /// **One deliberate divergence**: the deployed `acc.double()` is
    /// `acc.add(acc)`, which the extraction driver records as `Add(acc, acc)`
    /// with *two copies* of the accumulator tree — the tree doubles every
    /// iteration and the output would have `2^64` nodes, which neither the
    /// encoder nor the Lean fingerprint traversal can materialize (production
    /// wires are indices, so the shipped circuit never pays this). The instance
    /// uses `acc.scale(Coeff::Two)` instead, recorded as `Mul(Const 2, acc)`:
    /// equal in value, one reference, linear in size. The Lean reimpl
    /// (`Lift.stepCircuit`) mirrors this same shape, so the digest certifies the
    /// shipped output up to that one value-preserving rewrite — the same class
    /// of tree-encoding workaround as `group_scale`'s freshening, verified by
    /// inspection rather than by the fingerprint.
    ///
    /// Input wires: `bits[0..128]` (128 wires). Output: the lifted element.
    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let bit_wires: Vec<Expr<Fp>> = (0..128usize)
            .map(|_| dr.alloc_input_wires(1).into_iter().next().unwrap())
            .collect();

        // Same constants, in the same order, as `Endoscalar::lift`.
        let mut constant_term = (Fp::ZETA + Fp::ONE).double();
        let coeffs = [
            -Fp::from(2),
            Fp::ZETA - Fp::ONE,
            (Fp::ONE - Fp::ZETA).double(),
        ];

        let mut acc = Element::zero(dr);

        for i in 0..64usize {
            let n_wire = &bit_wires[2 * i];
            let e_wire = &bit_wires[2 * i + 1];

            // Inline `Boolean::and(n, e)`: one mul gate (`a * b = c`) plus two
            // `enforce_equal`s binding the gate's `a`/`b` wires to `n` and `e`.
            // The output `ne` is the gate's `c` wire.
            let (mul_a, mul_b, mul_c) = dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
            dr.enforce_equal(&mul_a, n_wire)?;
            dr.enforce_equal(&mul_b, e_wire)?;

            let n = Element::promote(n_wire.clone(), ExtractionDriver::<Fp>::just(|| Fp::ZERO));
            let e = Element::promote(e_wire.clone(), ExtractionDriver::<Fp>::just(|| Fp::ZERO));
            let ne = Element::promote(mul_c, ExtractionDriver::<Fp>::just(|| Fp::ZERO));

            // Deployed: `acc.double()` — see the divergence note above.
            acc = acc.scale(dr, Coeff::Two);
            constant_term = constant_term.double();
            constant_term += Fp::ONE;

            let n = n.scale(dr, Coeff::Arbitrary(coeffs[0]));
            let e = e.scale(dr, Coeff::Arbitrary(coeffs[1]));
            let ne = ne.scale(dr, Coeff::Arbitrary(coeffs[2]));

            acc = acc.add(dr, &n);
            acc = acc.add(dr, &e);
            acc = acc.add(dr, &ne);
        }

        let tmp = Element::constant(dr, constant_term);
        acc = acc.add(dr, &tmp);

        WireCollector::collect_from(&acc)
    }
}
