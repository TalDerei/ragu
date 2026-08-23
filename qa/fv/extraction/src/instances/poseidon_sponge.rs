use ff::PrimeField;
use ragu_arithmetic::PoseidonPermutation;
use ragu_pasta::{Fp, Fq, PoseidonFp, PoseidonFq};
use ragu_primitives::{Element, poseidon::Sponge};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

/// `Sponge::new` → `absorb(x)` → `squeeze()` over `PoseidonFp` (`T = 5`,
/// `RATE = 4`, `α = 5`, 8 full + 56 partial rounds): one permutation of the
/// state `[x, 0, 0, 0, 0]`, returning its first rate word.
///
/// Input wire: `x` (1 wire). Output: the squeezed element (1 wire).
pub struct PoseidonHash1InstanceFp;

impl CircuitInstance for PoseidonHash1InstanceFp {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        sponge_absorb_n::<Fp, PoseidonFp, 1>(dr, &PoseidonFp)
    }
}

/// As [`PoseidonHash1InstanceFp`] with a full rate block: `absorb` four
/// elements, then `squeeze` — still a single permutation, of the state
/// `[x₀, x₁, x₂, x₃, 0]`.
///
/// Input wires: `x₀, …, x₃` (4 wires). Output: the squeezed element (1 wire).
pub struct PoseidonHash4InstanceFp;

impl CircuitInstance for PoseidonHash4InstanceFp {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        sponge_absorb_n::<Fp, PoseidonFp, 4>(dr, &PoseidonFp)
    }
}

/// As [`PoseidonHash1InstanceFp`] over `PoseidonFq`, the other field of the
/// cycle: same shape, different round constants and MDS matrix.
pub struct PoseidonHash1InstanceFq;

impl CircuitInstance for PoseidonHash1InstanceFq {
    type Field = Fq;

    fn circuit(dr: &mut ExtractionDriver<Fq>) -> ragu_core::Result<Vec<Expr<Fq>>> {
        sponge_absorb_n::<Fq, PoseidonFq, 1>(dr, &PoseidonFq)
    }
}

/// Absorbs `N` input wires (at most `P::RATE`, so one permutation) into a
/// fresh sponge and squeezes one element.
fn sponge_absorb_n<F: PrimeField, P: PoseidonPermutation<F>, const N: usize>(
    dr: &mut ExtractionDriver<F>,
    params: &'static P,
) -> ragu_core::Result<Vec<Expr<F>>> {
    assert!(
        N <= P::RATE,
        "more than one block would need a second permutation"
    );
    let element_template = Element::constant(dr, F::ZERO);

    let mut sponge = Sponge::<'_, _, P>::new(dr, params);
    for _ in 0..N {
        let input_wires = dr.alloc_input_wires(1);
        let x = WireDeserializer::new(input_wires).into_gadget(&element_template)?;
        sponge.absorb(dr, &x)?;
    }
    let out = sponge.squeeze(dr)?;

    WireCollector::collect_from(&out)
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;
    use crate::{expr::Op, fingerprint::normalize};

    /// Statistics that shaped the Lean reimplementation: how large the
    /// extracted trace is and how many monomials the largest normalized
    /// constraint carries (the partial rounds' linear words must be flattened
    /// on the Lean side, see `Ragu/Circuits/Poseidon/Linear.lean`). Run with
    /// `cargo test -p lean_extraction -- --nocapture`.
    #[test]
    fn trace_stats() {
        let start = Instant::now();
        let trace = PoseidonHash1InstanceFp::extracted_trace();
        let extracted = start.elapsed();

        let mut witnesses = 0usize;
        let mut asserts = 0usize;
        let mut max_terms = 0usize;
        let mut total_terms = 0usize;
        for op in &trace.ops {
            match op {
                Op::Witness { count } => witnesses += count,
                Op::Assert(expr) => {
                    asserts += 1;
                    let terms = normalize(expr).terms().count();
                    total_terms += terms;
                    max_terms = max_terms.max(terms);
                }
            }
        }
        let output_terms: Vec<usize> = trace
            .outputs
            .iter()
            .map(|o| normalize(o).terms().count())
            .collect();
        let start = Instant::now();
        let digest = PoseidonHash1InstanceFp::fingerprint();
        let fingerprinted = start.elapsed();

        println!(
            "poseidon absorb1: ops={} witnesses={} asserts={} max_terms={} total_terms={} output_terms={:?}\n\
             extraction={extracted:?} fingerprint={fingerprinted:?} digest={digest}",
            trace.ops.len(),
            witnesses,
            asserts,
            max_terms,
            total_terms,
            output_terms,
        );
        assert_eq!(witnesses, 288 * 3);
        assert_eq!(asserts, 288 * 3);
    }
}
