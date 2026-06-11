//! Shared substrate for randomly generated gadget programs.
//!
//! Six fuzz targets in `qa/fuzz` independently grew the same idea: decode a
//! byte stream into a program over a stack of [`Element`]s (and [`Boolean`]s),
//! synthesize it through a [`Driver`], and check an invariant — robustness,
//! driver-vs-driver agreement, witness cheating, constraint-identity
//! acceptance, or patcher-style under-constraint hunting. Four of them carried
//! byte-identical copies of the op vocabulary; the other two carried subsets
//! plus a pinning op. This module is the single home for that machinery.
//!
//! # Layers
//!
//! Consumers pick the layers they need; nothing forces the full stack:
//!
//! 1. **AST** ([`Op`], [`OpKind`], [`Capabilities`], [`OpSet`], [`Preamble`]):
//!    a field-agnostic program representation with per-op capability metadata
//!    and per-consumer capability masks.
//! 2. **Decoding / generation**: a byte-stream decoder with *decode-time
//!    clamping* — ops outside the consumer's [`OpSet`] are remapped onto
//!    allowed ones, so any byte stream is a valid program for any consumer and
//!    corpora can cross-pollinate between fuzz targets — plus `proptest`
//!    strategies over the same AST for deterministic in-tree properties.
//! 3. **Synthesis**: one driver-generic interpreter emitting real gadget
//!    calls, with consumer-owned policy for fallible ops.
//! 4. **Native shadow**: an `F`-level evaluator mirroring each op's true
//!    semantics, for differential oracles.
//! 5. **Circuit wrapper**: a generated program as a registerable
//!    `Circuit`, with a satisfying-witness mode for constraint-level oracles.
//!
//! Layers 2–5 are introduced by their respective consumers' migrations; this
//! file currently provides layer 1.
//!
//! # Oracle policy is not generator policy
//!
//! The same op means different things to different harnesses: a robustness
//! target *wants* [`Op::Invert`] to receive zero and assert `Err`-not-panic; a
//! satisfying-witness consumer needs it steered to succeed; a metamorphic
//! target needs two drivers to fail identically. The substrate exposes raw
//! ops and capability metadata; what "expected" means stays in each harness.
//!
//! [`Element`]: ragu_primitives::Element
//! [`Boolean`]: ragu_primitives::Boolean
//! [`Driver`]: ragu_core::drivers::Driver

use ff::PrimeField;

/// One instruction of a generated gadget program.
///
/// Operand fields index the element stack (or, for boolean-typed operands,
/// the boolean stack) and are reduced modulo the live stack length at
/// execution time, so any payload is well-formed. Value payloads are
/// field-agnostic seeds (`u64`, special-value indices, or raw canonical
/// bytes) interpreted by the synthesis and shadow layers.
///
/// The vocabulary is the union of every `qa/fuzz` op-stream target:
/// the 19 ops shared by `fuzz_element_ops` / `fuzz_witness_cheat` /
/// `fuzz_driver_metamorphic` / `fuzz_witness_coverage`, plus [`Op::Anchor`]
/// from the patcher family (`fuzz_circuit_cheat` / `fuzz_advice_patcher`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    /// Push `elems[a] + elems[b]`.
    Add(u8, u8),
    /// Push `elems[a] - elems[b]`.
    Sub(u8, u8),
    /// Push `elems[a] * elems[b]` (one gate, two copy constraints).
    Mul(u8, u8),
    /// Push `elems[a]^2`.
    Square(u8),
    /// Push `2 * elems[a]`.
    Double(u8),
    /// Push `-elems[a]`.
    Negate(u8),
    /// Push `elems[a]^{-1}`; fails on zero.
    Invert(u8),
    /// Push a [`Boolean`](ragu_primitives::Boolean) indicating
    /// `elems[a] == 0` onto the boolean stack.
    IsZero(u8),
    /// Push `elems[a] / elems[b]`; fails when `elems[b]` is zero.
    Divide(u8, u8),
    /// Push `elems[a] * c` for the constant `c` (a virtual wire; no gate).
    Scale(u8, u64),
    /// Push `elems[a] * s + elems[b]` via Horner folding, where `s` is a
    /// freshly allocated scale element seeded from the `u64`.
    Fold(u8, u8, u64),
    /// Push the constant `v` (a virtual wire; no allocation).
    AllocConst(u64),
    /// Allocate an element holding [`special_value`] of the index.
    AllocSpecial(u8),
    /// Allocate `(root, root^2)` in a single gate via `Element::alloc_square`,
    /// with the root seeded from the `u64`. Pushes both.
    AllocSquare(u64),
    /// Allocate an element whose value is the 32-byte chunk interpreted as a
    /// canonical field element; skipped when non-canonical. Lets fuzzer
    /// dictionary entries land directly in the witness.
    AllocRaw([u8; 32]),
    /// Allocate a boolean with the given value onto the boolean stack.
    BoolAlloc(bool),
    /// Push `!bools[a]` onto the boolean stack.
    BoolNot(u8),
    /// Push `bools[a] & bools[b]` onto the boolean stack.
    BoolAnd(u8, u8),
    /// Push `bools[cond] ? elems[a] : elems[b]`.
    ConditionalSelect(u8, u8, u8),
    /// Pin `elems[a]` to its honest value via `enforce_zero(elem - const)`.
    ///
    /// The pinned constant is captured from an honest evaluation by the
    /// consumer (see the synthesis layer); anchors are what give the
    /// constraint-level oracles their rejection power.
    Anchor(u8),
}

/// Fieldless discriminant of [`Op`], used for capability lookups and
/// [`OpSet`] membership.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum OpKind {
    /// See [`Op::Add`].
    Add,
    /// See [`Op::Sub`].
    Sub,
    /// See [`Op::Mul`].
    Mul,
    /// See [`Op::Square`].
    Square,
    /// See [`Op::Double`].
    Double,
    /// See [`Op::Negate`].
    Negate,
    /// See [`Op::Invert`].
    Invert,
    /// See [`Op::IsZero`].
    IsZero,
    /// See [`Op::Divide`].
    Divide,
    /// See [`Op::Scale`].
    Scale,
    /// See [`Op::Fold`].
    Fold,
    /// See [`Op::AllocConst`].
    AllocConst,
    /// See [`Op::AllocSpecial`].
    AllocSpecial,
    /// See [`Op::AllocSquare`].
    AllocSquare,
    /// See [`Op::AllocRaw`].
    AllocRaw,
    /// See [`Op::BoolAlloc`].
    BoolAlloc,
    /// See [`Op::BoolNot`].
    BoolNot,
    /// See [`Op::BoolAnd`].
    BoolAnd,
    /// See [`Op::ConditionalSelect`].
    ConditionalSelect,
    /// See [`Op::Anchor`].
    Anchor,
}

impl OpKind {
    /// Every kind, in stable encoding order. The position of a kind in this
    /// array is its wire-format discriminant (see the decoding layer), so
    /// **append new kinds at the end** — reordering breaks corpus encodings.
    pub const ALL: [OpKind; 20] = [
        OpKind::Add,
        OpKind::Sub,
        OpKind::Mul,
        OpKind::Square,
        OpKind::Double,
        OpKind::Negate,
        OpKind::Invert,
        OpKind::IsZero,
        OpKind::Divide,
        OpKind::Scale,
        OpKind::Fold,
        OpKind::AllocConst,
        OpKind::AllocSpecial,
        OpKind::AllocSquare,
        OpKind::AllocRaw,
        OpKind::BoolAlloc,
        OpKind::BoolNot,
        OpKind::BoolAnd,
        OpKind::ConditionalSelect,
        OpKind::Anchor,
    ];

    /// Capability metadata for this kind.
    pub const fn capabilities(self) -> Capabilities {
        match self {
            OpKind::Add | OpKind::Sub | OpKind::Double | OpKind::Negate | OpKind::Scale => {
                Capabilities::SHADOWED
            }
            OpKind::Mul | OpKind::Square => Capabilities::SHADOWED.union(Capabilities::GATES),
            OpKind::Invert => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::VALUE_FALLIBLE),
            OpKind::Divide => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::VALUE_FALLIBLE),
            OpKind::IsZero => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::BOOLEAN),
            OpKind::Fold => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::ALLOCATES_ADVICE),
            OpKind::AllocConst => Capabilities::SHADOWED,
            OpKind::AllocSpecial => Capabilities::SHADOWED.union(Capabilities::ALLOCATES_ADVICE),
            OpKind::AllocSquare => Capabilities::SHADOWED
                .union(Capabilities::GATES)
                .union(Capabilities::ALLOCATES_ADVICE),
            OpKind::AllocRaw => Capabilities::SHADOWED
                .union(Capabilities::ALLOCATES_ADVICE)
                .union(Capabilities::VALUE_FALLIBLE),
            OpKind::BoolAlloc => Capabilities::SHADOWED
                .union(Capabilities::BOOLEAN)
                .union(Capabilities::GATES)
                .union(Capabilities::ALLOCATES_ADVICE),
            OpKind::BoolNot => Capabilities::SHADOWED.union(Capabilities::BOOLEAN),
            OpKind::BoolAnd => Capabilities::SHADOWED
                .union(Capabilities::BOOLEAN)
                .union(Capabilities::GATES),
            OpKind::ConditionalSelect => Capabilities::SHADOWED
                .union(Capabilities::BOOLEAN)
                .union(Capabilities::GATES),
            OpKind::Anchor => Capabilities::SHADOWED.union(Capabilities::ANCHORS),
        }
    }
}

impl Op {
    /// The fieldless discriminant of this op.
    pub const fn kind(self) -> OpKind {
        match self {
            Op::Add(..) => OpKind::Add,
            Op::Sub(..) => OpKind::Sub,
            Op::Mul(..) => OpKind::Mul,
            Op::Square(..) => OpKind::Square,
            Op::Double(..) => OpKind::Double,
            Op::Negate(..) => OpKind::Negate,
            Op::Invert(..) => OpKind::Invert,
            Op::IsZero(..) => OpKind::IsZero,
            Op::Divide(..) => OpKind::Divide,
            Op::Scale(..) => OpKind::Scale,
            Op::Fold(..) => OpKind::Fold,
            Op::AllocConst(..) => OpKind::AllocConst,
            Op::AllocSpecial(..) => OpKind::AllocSpecial,
            Op::AllocSquare(..) => OpKind::AllocSquare,
            Op::AllocRaw(..) => OpKind::AllocRaw,
            Op::BoolAlloc(..) => OpKind::BoolAlloc,
            Op::BoolNot(..) => OpKind::BoolNot,
            Op::BoolAnd(..) => OpKind::BoolAnd,
            Op::ConditionalSelect(..) => OpKind::ConditionalSelect,
            Op::Anchor(..) => OpKind::Anchor,
        }
    }
}

/// Per-op capability flags consulted when intersecting an op vocabulary with
/// a consumer's requirements.
///
/// Flags describe what an op *does or needs*, not whether a consumer wants
/// it; consumers express wants via [`OpSet`] masks built from these flags.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Capabilities(u16);

impl Capabilities {
    /// The op has a faithful native (out-of-circuit) mirror in the shadow
    /// evaluator. Differential oracles require this; the invariant-based
    /// oracle does not. Every current op is shadowed; the flag exists so
    /// future routine-backed ops can opt out without API change.
    pub const SHADOWED: Capabilities = Capabilities(1 << 0);

    /// The op can fail for *value* reasons (inverting zero, dividing by
    /// zero, non-canonical raw bytes) — as opposed to the API-level
    /// fallibility of gate allocation, which never fires under honest
    /// witnesses. Satisfying-witness consumers must steer or exclude these.
    pub const VALUE_FALLIBLE: Capabilities = Capabilities(1 << 1);

    /// The op allocates fresh *advice* — wires a malicious prover chooses
    /// freely. These are the patcher family's mutation targets.
    pub const ALLOCATES_ADVICE: Capabilities = Capabilities(1 << 2);

    /// The op reads or writes the boolean stack.
    pub const BOOLEAN: Capabilities = Capabilities(1 << 3);

    /// The op emits at least one multiplication gate.
    pub const GATES: Capabilities = Capabilities(1 << 4);

    /// The op emits a pinning constraint against an honest constant
    /// ([`Op::Anchor`]). Only meaningful to consumers that compute honest
    /// evaluations first.
    pub const ANCHORS: Capabilities = Capabilities(1 << 5);

    /// The op synthesizes through a [`Routine`](ragu_core::routines::Routine).
    /// No current op does; reserved for Poseidon-style grammar growth, where
    /// drivers without routine support must exclude it.
    pub const ROUTINES: Capabilities = Capabilities(1 << 6);

    /// The empty capability set.
    pub const fn empty() -> Capabilities {
        Capabilities(0)
    }

    /// The union of two capability sets.
    pub const fn union(self, other: Capabilities) -> Capabilities {
        Capabilities(self.0 | other.0)
    }

    /// Whether every flag in `other` is present in `self`.
    pub const fn contains(self, other: Capabilities) -> bool {
        self.0 & other.0 == other.0
    }

    /// Whether any flag in `other` is present in `self`.
    pub const fn intersects(self, other: Capabilities) -> bool {
        self.0 & other.0 != 0
    }
}

/// A consumer's allowed-op mask: which [`OpKind`]s the decoder may emit.
///
/// Masks are how "one rich union grammar, callers choose" works in practice:
/// the decoder clamps disallowed kinds onto allowed ones at decode time, so
/// the byte encoding — and therefore the corpus — stays shared across
/// consumers with different masks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OpSet(u32);

impl OpSet {
    /// Every op in the vocabulary. The robustness targets' mask.
    pub const ALL: OpSet = OpSet((1 << OpKind::ALL.len()) - 1);

    /// Builds a set from a predicate over kinds.
    pub fn filtered(allow: impl Fn(OpKind) -> bool) -> OpSet {
        let mut bits = 0u32;
        for (i, kind) in OpKind::ALL.iter().enumerate() {
            if allow(*kind) {
                bits |= 1 << i;
            }
        }
        OpSet(bits)
    }

    /// Ops excluded: removes every kind whose capabilities intersect `caps`.
    pub fn without(self, caps: Capabilities) -> OpSet {
        let mut bits = self.0;
        for (i, kind) in OpKind::ALL.iter().enumerate() {
            if kind.capabilities().intersects(caps) {
                bits &= !(1 << i);
            }
        }
        OpSet(bits)
    }

    /// Whether `kind` is allowed by this set.
    pub fn allows(self, kind: OpKind) -> bool {
        let idx = OpKind::ALL
            .iter()
            .position(|k| *k == kind)
            .expect("OpKind::ALL is exhaustive over the enum, so every kind has a position");
        self.0 & (1 << idx) != 0
    }

    /// The allowed kinds, in stable encoding order. Decoders index into this
    /// to clamp a raw discriminant onto an allowed kind.
    pub fn allowed_kinds(self) -> impl Iterator<Item = OpKind> {
        OpKind::ALL
            .into_iter()
            .enumerate()
            .filter(move |(i, _)| self.0 & (1 << i) != 0)
            .map(|(_, k)| k)
    }

    /// Number of allowed kinds.
    pub fn len(self) -> usize {
        self.0.count_ones() as usize
    }

    /// Whether no kinds are allowed.
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }
}

/// The shared recipe for a program's initial element stack, lifted from the
/// four robustness targets: plain `u64` seeds, multi-limb large values,
/// special-value entries, and a mask choosing constant vs. witness
/// allocation per slot.
#[derive(Clone, Debug)]
pub struct Preamble {
    /// Plain seeds, each becoming one initial element.
    pub seeds: [u64; 4],
    /// Multi-limb seeds combined as `l0 + l1·2^32 + l2·2^48 + l3·2^56`,
    /// reaching values outside the `u64` range.
    pub large_seeds: [[u64; 4]; 2],
    /// Indices into [`special_value`] for two extra initial elements.
    pub special_seeds: [u8; 2],
    /// If bit `i % 8` is set, initial element `i` is created as a constant
    /// (virtual wire) instead of an allocated witness wire.
    pub constant_mask: u8,
}

impl Preamble {
    /// Number of initial elements a preamble produces.
    pub const LEN: usize = 4 + 2 + 2;

    /// The initial element values, in stack order.
    pub fn values<F: PrimeField>(&self) -> [F; Self::LEN] {
        let mut out = [F::ZERO; Self::LEN];
        let mut i = 0;
        for seed in self.seeds {
            out[i] = F::from(seed);
            i += 1;
        }
        for ls in self.large_seeds {
            out[i] = F::from(ls[0])
                + F::from(ls[1]) * F::from(1u64 << 32)
                + F::from(ls[2]) * F::from(1u64 << 48)
                + F::from(ls[3]) * F::from(1u64 << 56);
            i += 1;
        }
        for ss in self.special_seeds {
            out[i] = special_value(ss);
            i += 1;
        }
        out
    }

    /// Whether initial element `i` is a constant (vs. an allocated witness
    /// wire).
    pub fn is_constant(&self, i: usize) -> bool {
        self.constant_mask & (1 << (i % 8)) != 0
    }
}

/// Structurally interesting field values, indexed by a fuzzer-chosen byte.
///
/// The 16-variant superset used by the robustness targets (the patcher
/// family previously used an 8-variant subset).
pub fn special_value<F: PrimeField>(idx: u8) -> F {
    match idx % 16 {
        0 => F::ZERO,
        1 => F::ONE,
        2 => -F::ONE,     // p - 1
        3 => -F::from(2), // p - 2
        4 => F::TWO_INV,  // (p + 1) / 2
        5 => F::from(2),
        6 => F::from(3),
        7 => F::from(7),
        8 => F::ROOT_OF_UNITY,                      // 2-adic primitive root
        9 => F::ROOT_OF_UNITY.square(),             // (S-1)-adic primitive root
        10 => F::ROOT_OF_UNITY.pow_vartime([4u64]), // (S-2)-adic primitive root
        11 => F::MULTIPLICATIVE_GENERATOR,          // smallest generator
        12 => F::MULTIPLICATIVE_GENERATOR.square(),
        13 => F::from(1u64 << 32), // 2^32 boundary
        14 => F::from(1u64 << 48), // 2^48 boundary
        _ => F::from(u64::MAX),    // large value near 2^64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `OpKind::ALL` must cover every variant exactly once; the encoding
    /// order is load-bearing for corpus stability.
    #[test]
    fn all_kinds_exhaustive_and_unique() {
        for (i, a) in OpKind::ALL.iter().enumerate() {
            for b in OpKind::ALL.iter().skip(i + 1) {
                assert_ne!(a, b, "duplicate kind in OpKind::ALL");
            }
        }
        // Compile-time exhaustiveness: a match over every variant. Adding a
        // variant without extending `ALL` fails the uniqueness/position
        // assertions in `opset_round_trips` below.
        for kind in OpKind::ALL {
            match kind {
                OpKind::Add
                | OpKind::Sub
                | OpKind::Mul
                | OpKind::Square
                | OpKind::Double
                | OpKind::Negate
                | OpKind::Invert
                | OpKind::IsZero
                | OpKind::Divide
                | OpKind::Scale
                | OpKind::Fold
                | OpKind::AllocConst
                | OpKind::AllocSpecial
                | OpKind::AllocSquare
                | OpKind::AllocRaw
                | OpKind::BoolAlloc
                | OpKind::BoolNot
                | OpKind::BoolAnd
                | OpKind::ConditionalSelect
                | OpKind::Anchor => {}
            }
        }
    }

    #[test]
    fn opset_round_trips() {
        assert_eq!(OpSet::ALL.len(), OpKind::ALL.len());
        for kind in OpKind::ALL {
            assert!(OpSet::ALL.allows(kind));
        }

        let no_bools = OpSet::ALL.without(Capabilities::BOOLEAN);
        let bool_kinds = OpKind::ALL
            .iter()
            .filter(|k| k.capabilities().intersects(Capabilities::BOOLEAN))
            .count();
        assert_eq!(no_bools.len(), OpKind::ALL.len() - bool_kinds);
        for kind in OpKind::ALL {
            assert_eq!(
                no_bools.allows(kind),
                !kind.capabilities().intersects(Capabilities::BOOLEAN),
            );
        }

        let filtered = OpSet::filtered(|k| matches!(k, OpKind::Add | OpKind::Anchor));
        assert_eq!(filtered.len(), 2);
        assert!(filtered.allows(OpKind::Add));
        assert!(filtered.allows(OpKind::Anchor));
        assert!(!filtered.allows(OpKind::Mul));
        assert!(OpSet::filtered(|_| false).is_empty());
    }

    #[test]
    fn capability_table_sanity() {
        // Every current op is shadowed.
        for kind in OpKind::ALL {
            assert!(
                kind.capabilities().contains(Capabilities::SHADOWED),
                "{kind:?} should be shadow-supported",
            );
        }
        // The value-fallible set is exactly the three ops with value-dependent
        // failure modes.
        let fallible: Vec<OpKind> = OpSet::ALL
            .allowed_kinds()
            .filter(|k| k.capabilities().contains(Capabilities::VALUE_FALLIBLE))
            .collect();
        assert_eq!(fallible, [OpKind::Invert, OpKind::Divide, OpKind::AllocRaw],);
        // Anchor is the only anchoring op, and the patcher mutation targets
        // are exactly the advice allocators.
        let anchors: Vec<OpKind> = OpSet::ALL
            .allowed_kinds()
            .filter(|k| k.capabilities().contains(Capabilities::ANCHORS))
            .collect();
        assert_eq!(anchors, [OpKind::Anchor]);
        let advice: Vec<OpKind> = OpSet::ALL
            .allowed_kinds()
            .filter(|k| k.capabilities().contains(Capabilities::ALLOCATES_ADVICE))
            .collect();
        assert_eq!(
            advice,
            [
                OpKind::Fold,
                OpKind::AllocSpecial,
                OpKind::AllocSquare,
                OpKind::AllocRaw,
                OpKind::BoolAlloc,
            ],
        );
    }

    #[test]
    fn op_kind_agreement() {
        let ops = [
            Op::Add(0, 1),
            Op::Sub(0, 1),
            Op::Mul(0, 1),
            Op::Square(0),
            Op::Double(0),
            Op::Negate(0),
            Op::Invert(0),
            Op::IsZero(0),
            Op::Divide(0, 1),
            Op::Scale(0, 2),
            Op::Fold(0, 1, 2),
            Op::AllocConst(2),
            Op::AllocSpecial(3),
            Op::AllocSquare(2),
            Op::AllocRaw([0; 32]),
            Op::BoolAlloc(true),
            Op::BoolNot(0),
            Op::BoolAnd(0, 1),
            Op::ConditionalSelect(0, 1, 2),
            Op::Anchor(0),
        ];
        for (op, kind) in ops.iter().zip(OpKind::ALL) {
            assert_eq!(op.kind(), kind);
        }
    }
}
