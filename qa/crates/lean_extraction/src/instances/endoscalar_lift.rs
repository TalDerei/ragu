use ff::{Field, WithSmallOrderMulGroup};
use ragu_arithmetic::Coeff;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, boolean_from_wire},
};

pub struct EndoscalarLiftInstance;

impl CircuitInstance for EndoscalarLiftInstance {
    type Field = Fp;

    /// Mirrors `Endoscalar::lift` line for line: the 128 input wires are wrapped
    /// as `Boolean`s (see [`boolean_from_wire`]) and every operation is the
    /// deployed gadget's own call — `Boolean::and`, `Element::{zero, scale,
    /// add, constant}` — in the deployed order.
    ///
    /// The body is still mirrored rather than invoked: an `Endoscalar` could be
    /// assembled from the input wires the same way (an `unstable-fv`
    /// constructor, like `fv_utils::boolean_unchecked`), but the real
    /// `Endoscalar::lift` would then record its accumulator as an exponentially
    /// large tree; see the divergence note.
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

            let n = boolean_from_wire(n_wire.clone());
            let e = boolean_from_wire(e_wire.clone());
            let ne = n.and(dr, &e)?;

            // Deployed: `acc.double()` — see the divergence note above.
            acc = acc.scale(dr, Coeff::Two);
            constant_term = constant_term.double();
            constant_term += Fp::ONE;

            let n = n.element().scale(dr, Coeff::Arbitrary(coeffs[0]));
            let e = e.element().scale(dr, Coeff::Arbitrary(coeffs[1]));
            let ne = ne.element().scale(dr, Coeff::Arbitrary(coeffs[2]));

            acc = acc.add(dr, &n);
            acc = acc.add(dr, &e);
            acc = acc.add(dr, &ne);
        }

        let tmp = Element::constant(dr, constant_term);
        acc = acc.add(dr, &tmp);

        WireCollector::collect_from(&acc)
    }
}
