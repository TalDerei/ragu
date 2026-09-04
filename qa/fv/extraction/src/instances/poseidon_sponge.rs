use ff::{Field, PrimeField};
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

/// Two full rate blocks absorbed, then three squeezes.
///
/// This is the shape `PoseidonHash{1,4}Instance*` cannot reach. Absorbing a
/// 5th element makes Rust permute the buffered block and start a new one, so
/// eight elements run *two* permutations over the same state — which is where
/// a bug that contaminated the capacity word across a block boundary would
/// show up. The three squeezes then come out of one permutation without
/// triggering another (`get_rate` reverses the rate words and `squeeze` pops
/// the last), pinning that the i-th squeezed element is state word i.
///
/// Input wires: `x₀ … x₇` (8 wires). Outputs: three squeezed elements.
pub struct PoseidonBlocks2Squeeze3InstanceFp;

impl CircuitInstance for PoseidonBlocks2Squeeze3InstanceFp {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        sponge_blocks::<Fp, PoseidonFp, 8, 3>(dr, &PoseidonFp)
    }
}

/// Six absorbs, then two squeezes: one full rate block and a two-element
/// tail, so the sponge permutes at the block boundary and again on the
/// short tail at `squeeze` — the ragged shape `PoseidonBlocks2Squeeze3InstanceFp`
/// cannot reach. Ties to the Lean `Sponge.Ragged` family.
///
/// Input wires: `x₀ … x₅` (6 wires). Outputs: two squeezed elements.
pub struct PoseidonBlocks1Tail2InstanceFp;

impl CircuitInstance for PoseidonBlocks1Tail2InstanceFp {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        sponge_blocks::<Fp, PoseidonFp, 6, 2>(dr, &PoseidonFp)
    }
}

/// `absorb(x)` → `save_state` → `resume` → `squeeze()`: the `Transcript`
/// API's path through the sponge. Trace-identical to
/// [`PoseidonHash1InstanceFp`] — `save_state` runs the permutation the
/// first `squeeze` would, `resume` re-enters squeeze mode on that state —
/// so the Lean instance is `Hash1Fp`'s; what this pins is that the
/// save/resume path emits the same trace as the direct one.
pub struct PoseidonSaveResumeInstanceFp;

impl CircuitInstance for PoseidonSaveResumeInstanceFp {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let element_template = Element::constant(dr, Fp::ZERO);
        let input_wires = dr.alloc_input_wires(1);
        let x = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        let mut sponge = Sponge::<'_, _, PoseidonFp>::new(dr, &PoseidonFp);
        sponge.absorb(dr, &x)?;
        let state = sponge
            .save_state(dr)
            .expect("one element was absorbed and nothing squeezed");
        let mut sponge = Sponge::resume(state, &PoseidonFp);
        let out = sponge.squeeze(dr)?;

        WireCollector::collect_from(&out)
    }
}

/// `absorb(x)` → `squeeze()` → `absorb(y)` → `squeeze()`: absorption after
/// a squeeze. The second `absorb` re-enters absorb mode on the permuted
/// state, so the second `squeeze` permutes `state + [y]` — two permutations
/// over two width-1 batches, the narrow-block reading of the Lean `Squeeze`
/// family. Only the final squeeze is collected; the first is word `0` of the
/// intermediate state, which `Hash1Fp` pins.
///
/// Input wires: `x, y` (2 wires). Output: the final squeezed element.
pub struct PoseidonInterleavedInstanceFp;

impl CircuitInstance for PoseidonInterleavedInstanceFp {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let element_template = Element::constant(dr, Fp::ZERO);
        let x_wires = dr.alloc_input_wires(1);
        let x = WireDeserializer::new(x_wires).into_gadget(&element_template)?;
        let y_wires = dr.alloc_input_wires(1);
        let y = WireDeserializer::new(y_wires).into_gadget(&element_template)?;

        let mut sponge = Sponge::<'_, _, PoseidonFp>::new(dr, &PoseidonFp);
        sponge.absorb(dr, &x)?;
        let _first = sponge.squeeze(dr)?;
        sponge.absorb(dr, &y)?;
        let out = sponge.squeeze(dr)?;

        WireCollector::collect_from(&out)
    }
}

/// Absorbs `N` elements consecutively — `N` may exceed `P::RATE`, in which
/// case the sponge permutes at each block boundary — and squeezes `S`
/// elements. On the Lean side a multiple of `RATE` is `Sponge.Blocks`
/// (uniform full blocks); anything else is `Sponge.Ragged` (full blocks plus
/// a short tail).
fn sponge_blocks<F: PrimeField, P: PoseidonPermutation<F>, const N: usize, const S: usize>(
    dr: &mut ExtractionDriver<F>,
    params: &'static P,
) -> ragu_core::Result<Vec<Expr<F>>> {
    assert!(N > 0, "the Rust sponge refuses to squeeze before an absorb");
    assert!(S > 0, "the final permutation is run by the first squeeze");
    assert!(
        S <= P::RATE,
        "more squeezes than the rate would permute again"
    );
    let element_template = Element::constant(dr, F::ZERO);

    let mut sponge = Sponge::<'_, _, P>::new(dr, params);
    for _ in 0..N {
        let input_wires = dr.alloc_input_wires(1);
        let x = WireDeserializer::new(input_wires).into_gadget(&element_template)?;
        sponge.absorb(dr, &x)?;
    }

    let mut outputs = Vec::new();
    for _ in 0..S {
        let out = sponge.squeeze(dr)?;
        outputs.extend(WireCollector::collect_from(&out)?);
    }

    Ok(outputs)
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
