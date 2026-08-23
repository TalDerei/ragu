use ragu_pasta::{Fp, PoseidonFp};
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
///
/// Not yet an export target: the Lean reimplementation is in progress (see
/// `qa/lean/CHECKLIST.md` §2), so until then this instance only backs the
/// `trace_stats` spike test.
#[cfg_attr(not(test), allow(dead_code))]
pub struct PoseidonSpongeAbsorb1Instance;

impl CircuitInstance for PoseidonSpongeAbsorb1Instance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        sponge_absorb_n::<1>(dr)
    }
}

/// Absorbs `N` input wires (at most `RATE`, so one permutation) and squeezes
/// one element.
#[cfg_attr(not(test), allow(dead_code))]
fn sponge_absorb_n<const N: usize>(
    dr: &mut ExtractionDriver<Fp>,
) -> ragu_core::Result<Vec<Expr<Fp>>> {
    let element_template = Element::constant(dr, Fp::zero());

    let mut sponge = Sponge::<'_, _, PoseidonFp>::new(dr, &PoseidonFp);
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

    /// Spike statistics for the Poseidon design: how large the extracted
    /// trace is and how many monomials the largest normalized constraint
    /// carries. Run with `cargo test -p lean_extraction -- --nocapture`.
    #[test]
    fn trace_stats() {
        let start = Instant::now();
        let trace = PoseidonSpongeAbsorb1Instance::extracted_trace();
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
        let digest = PoseidonSpongeAbsorb1Instance::fingerprint();
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
