//! Structured circuit idioms (issue #793 follow-up).
//!
//! Random op-soup from [`Program::decode`](super::Program::decode) almost
//! never assembles the *shapes* real circuits are built from — a long
//! dependency chain whose final wire is observed, a multiply-accumulate
//! pipeline, a decompose-then-recompose, a conditional gate. Those idioms
//! are where soundness bugs actually live, so this module builds them
//! directly from the real op vocabulary, each ending in an [`Op::Anchor`] on
//! its result so a cheat that perturbs any input is *observable*.
//!
//! The builders are deterministic functions of a `u64` seed, usable three
//! ways: as proptest inputs ([`idiom_strategy`]), as a fixed battery
//! ([`idiom_programs`]), and — via [`Program::encode`](super::Program::encode)
//! — as libFuzzer corpus seeds ([`idiom_seed_corpus`]).

use proptest::{prelude::*, sample::select, strategy::BoxedStrategy};

use super::{Op, Preamble, Program};

/// A preamble whose eight slots are all free witness advice (so every input
/// to an idiom can be cheated), seeded from `seed`.
fn advice_preamble(seed: u64) -> Preamble {
    let s = seed | 1; // avoid an all-zero seed degenerating values
    Preamble {
        seeds: [s, s ^ 0x9e37, s.wrapping_mul(3) | 1, s.rotate_left(17) | 1],
        large_seeds: [[s, 2, 3, 4], [5, 6, 7, s ^ 8]],
        special_seeds: [(seed & 7) as u8, ((seed >> 3) & 7) as u8],
        constant_mask: 0, // all eight preamble slots are free advice
    }
}

/// Incrementally builds a program, tracking the live element-stack length so
/// operand indices always reference existing wires.
struct Builder {
    ops: Vec<Op>,
    len: usize,
}

impl Builder {
    fn new() -> Self {
        // Synthesis starts with the eight preamble elements on the stack.
        Builder {
            ops: Vec::new(),
            len: Preamble::LEN,
        }
    }

    /// Pushes an op that grows the element stack by one and returns the index
    /// of the new top.
    fn push(&mut self, op: Op) -> u8 {
        self.ops.push(op);
        let idx = self.len;
        self.len += 1;
        idx as u8
    }

    /// Anchors `slot` (observing it) and finishes.
    fn finish(mut self, slot: u8) -> Vec<Op> {
        self.ops.push(Op::Anchor(slot));
        self.ops
    }
}

/// A deep arithmetic dependency chain: alternating `Mul`/`Add`/`Square`/
/// `Double` folded over the preamble, ending in an anchor on the final wire.
/// A cheat on any early input must propagate through the whole chain to be
/// caught — the patcher's repair depth under stress.
pub fn deep_chain(seed: u64) -> Program {
    let mut b = Builder::new();
    let mut top = (seed % Preamble::LEN as u64) as u8;
    for i in 0..12u64 {
        let other = ((seed >> i) % Preamble::LEN as u64) as u8;
        top = match (seed >> (i * 2)) & 3 {
            0 => b.push(Op::Mul(top, other)),
            1 => b.push(Op::Add(top, other)),
            2 => b.push(Op::Square(top)),
            _ => b.push(Op::Double(top)),
        };
    }
    Program {
        preamble: advice_preamble(seed),
        ops: b.finish(top),
    }
}

/// A multiply-accumulate pipeline: `acc += aᵢ · bᵢ` over several preamble
/// pairs, ending in an anchor on the accumulator. Each product feeds the
/// running sum, so the accumulator wire pins a fan-in of inputs.
pub fn multiply_accumulate(seed: u64) -> Program {
    let mut b = Builder::new();
    let p = Preamble::LEN as u64;
    let mut acc = b.push(Op::Mul((seed % p) as u8, ((seed >> 8) % p) as u8));
    for i in 1..5u64 {
        let x = ((seed >> (i * 4)) % p) as u8;
        let y = ((seed >> (i * 4 + 2)) % p) as u8;
        let prod = b.push(Op::Mul(x, y));
        acc = b.push(Op::Add(acc, prod));
    }
    Program {
        preamble: advice_preamble(seed),
        ops: b.finish(acc),
    }
}

/// A decompose-then-recompose idiom: weight several preamble "limbs" by
/// distinct `Scale` constants and sum them into a single recomposed value,
/// anchored. Mirrors limb recomposition, where a missing constraint on one
/// limb is a classic soundness bug.
pub fn decompose_recompose(seed: u64) -> Program {
    let mut b = Builder::new();
    let p = Preamble::LEN as u64;
    let weights = [1u64, 1 << 16, 1 << 32, 1 << 48];
    let mut acc = b.push(Op::Scale((seed % p) as u8, weights[0]));
    for (i, w) in weights.iter().enumerate().skip(1) {
        let limb = ((seed >> (i * 5)) % p) as u8;
        let scaled = b.push(Op::Scale(limb, *w));
        acc = b.push(Op::Add(acc, scaled));
    }
    Program {
        preamble: advice_preamble(seed),
        ops: b.finish(acc),
    }
}

/// A conditional-gating idiom: allocate a boolean, compute two arithmetic
/// branches, select between them, and anchor the result. Exercises the
/// boolean and `ConditionalSelect` paths a flat op-soup rarely composes.
///
/// (`ConditionalSelect` is outside the advice-patcher's repair vocabulary,
/// but this idiom is exercised by the completeness and revdot targets and is
/// a realistic shape worth seeding.)
pub fn conditional_gating(seed: u64) -> Program {
    let mut b = Builder::new();
    let p = Preamble::LEN as u64;
    let x = (seed % p) as u8;
    let y = ((seed >> 8) % p) as u8;
    let then_branch = b.push(Op::Mul(x, y));
    let else_branch = b.push(Op::Add(x, y));
    b.ops.push(Op::BoolAlloc(seed & 1 == 1)); // boolean stack slot 0
    let selected = b.push(Op::ConditionalSelect(0, then_branch, else_branch));
    Program {
        preamble: advice_preamble(seed),
        ops: b.finish(selected),
    }
}

/// Every idiom builder, in a stable order.
pub const IDIOM_BUILDERS: [fn(u64) -> Program; 4] = [
    deep_chain,
    multiply_accumulate,
    decompose_recompose,
    conditional_gating,
];

/// A fixed battery of idiom programs over a spread of seeds — a deterministic
/// suite for tests and corpus seeding.
pub fn idiom_programs() -> Vec<Program> {
    let seeds = [1u64, 2, 7, 42, 0xdead_beef, 0x1234_5678_9abc_def0];
    IDIOM_BUILDERS
        .iter()
        .flat_map(|build| seeds.iter().map(move |s| build(*s)))
        .collect()
}

/// Encoded ([`Program::encode`](super::Program::encode)) idiom programs,
/// ready to drop into a libFuzzer corpus directory so the fuzzer starts from
/// realistic shapes instead of discovering them by chance.
pub fn idiom_seed_corpus() -> Vec<Vec<u8>> {
    idiom_programs().iter().map(Program::encode).collect()
}

/// A proptest strategy drawing a random idiom from a random seed.
pub fn idiom_strategy() -> BoxedStrategy<Program> {
    (select(IDIOM_BUILDERS.to_vec()), any::<u64>())
        .prop_map(|(build, seed)| build(seed))
        .boxed()
}
