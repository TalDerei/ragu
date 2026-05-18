//! Algebraic-identity fuzz target.
//!
//! Generates random `Fp` pairs `(a, b)` and a Boolean `bv`, allocates them
//! as gadgets through `Simulator`, and asserts that a fixed list of
//! algebraic identities hold for every input. Any failure means a gadget
//! has broken the algebraic contract it claims to implement.
//!
//! This is property-based testing in fuzz-target form: the identities are
//! checked exhaustively over the input space `Vec<Op>`-style harnesses
//! can't easily probe, because they require running both sides of an
//! equation under the *same* witness and comparing the resulting wire
//! values. The Simulator does this naturally — it stores the assigned
//! `Fp` value on every wire, so `Element::value().take()` retrieves the
//! exact witness value the gadget produced.
//!
//! # Identities (Element)
//!
//! - additive commutativity: `a + b == b + a`
//! - additive identity:      `a + 0 == a`
//! - additive inverse:       `a + (-a) == 0`
//! - multiplicative commutativity: `a * b == b * a`
//! - multiplicative identity: `a * 1 == a`
//! - multiplicative annihilator: `a * 0 == 0`
//! - subtract self:          `a - a == 0`
//! - double negation:        `-(-a) == a`
//! - double == add self:     `Element::double(a) == a + a`
//! - square == mul self:     `Element::square(a) == a * a`
//! - distributivity:         `a * (b + 1) == a * b + a`
//!
//! # Identities (Boolean)
//!
//! - double not:             `!!bv == bv`
//! - self and:               `bv & bv == bv`
//!
//! # Identities (ConditionalSelect)
//!
//! Ragu's convention (`Boolean::conditional_select(&self, dr, a, b)`) is
//! `result = a + cond * (b - a)` — so `cond=false → a`, `cond=true → b`.
//!
//! - false select:           `cond_select(false, a, b) == a`
//! - true select:            `cond_select(true, a, b) == b`
//!
//! If any assertion fails, libFuzzer records a crash with the input
//! that triggered it.

#![no_main]

use arbitrary::Arbitrary;
use ff::{Field, PrimeField};
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_core::maybe::Maybe;
use ragu_primitives::{Boolean, Element, Simulator, allocator::Standard};

#[derive(Arbitrary, Debug)]
struct Input {
    /// 32 raw bytes parsed as canonical Fp via from_repr.
    a_bytes: [u8; 32],
    /// 32 raw bytes parsed as canonical Fp via from_repr.
    b_bytes: [u8; 32],
    /// Boolean witness for the Boolean-side identities.
    bv: bool,
}

/// Parse 32 bytes as a canonical Fp, falling back to a low-entropy
/// u64-derived value if the bytes don't form a valid field element.
/// This way every input is usable, including ones from libFuzzer's
/// random byte mutation.
fn parse_fp(bytes: [u8; 32]) -> Fp {
    Option::<Fp>::from(Fp::from_repr(bytes)).unwrap_or_else(|| {
        Fp::from(u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    })
}

fuzz_target!(|input: Input| {
    let a_val = parse_fp(input.a_bytes);
    let b_val = parse_fp(input.b_bytes);
    let bv_val = input.bv;

    let witness_data = (a_val, b_val, bv_val);

    let _ = Simulator::<Fp>::simulate(witness_data, |dr, witness| {
        let allocator = &mut Standard::new();

        let a = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.0))?;
        let b = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.1))?;
        let bv = Boolean::alloc(dr, allocator, witness.as_ref().map(|w| w.2))?;
        let zero = Element::constant(dr, Fp::ZERO);
        let one = Element::constant(dr, Fp::ONE);

        // ------------------------------------------------------------------
        // Element identities
        // ------------------------------------------------------------------

        // additive commutativity
        let lhs = a.add(dr, &b);
        let rhs = b.add(dr, &a);
        assert_eq!(
            *lhs.value().take(),
            *rhs.value().take(),
            "add commutativity failed: a={:?} b={:?}",
            a_val,
            b_val,
        );

        // additive identity
        let lhs = a.add(dr, &zero);
        assert_eq!(
            *lhs.value().take(),
            a_val,
            "additive identity failed: a={:?}",
            a_val,
        );

        // additive inverse
        let neg_a = a.negate(dr);
        let sum = a.add(dr, &neg_a);
        assert_eq!(
            *sum.value().take(),
            Fp::ZERO,
            "additive inverse failed: a={:?}",
            a_val,
        );

        // multiplicative commutativity
        let lhs = a.mul(dr, &b)?;
        let rhs = b.mul(dr, &a)?;
        assert_eq!(
            *lhs.value().take(),
            *rhs.value().take(),
            "mul commutativity failed: a={:?} b={:?}",
            a_val,
            b_val,
        );

        // multiplicative identity
        let lhs = a.mul(dr, &one)?;
        assert_eq!(
            *lhs.value().take(),
            a_val,
            "multiplicative identity failed: a={:?}",
            a_val,
        );

        // multiplicative annihilator
        let lhs = a.mul(dr, &zero)?;
        assert_eq!(
            *lhs.value().take(),
            Fp::ZERO,
            "multiplicative annihilator failed: a={:?}",
            a_val,
        );

        // subtract self
        let diff = a.sub(dr, &a);
        assert_eq!(
            *diff.value().take(),
            Fp::ZERO,
            "subtract self failed: a={:?}",
            a_val,
        );

        // double negation
        let neg_a = a.negate(dr);
        let neg_neg_a = neg_a.negate(dr);
        assert_eq!(
            *neg_neg_a.value().take(),
            a_val,
            "double negation failed: a={:?}",
            a_val,
        );

        // double == add self
        let doubled = a.double(dr);
        let added = a.add(dr, &a);
        assert_eq!(
            *doubled.value().take(),
            *added.value().take(),
            "double != add self: a={:?}",
            a_val,
        );

        // square == mul self
        let squared = a.square(dr)?;
        let mul_self = a.mul(dr, &a)?;
        assert_eq!(
            *squared.value().take(),
            *mul_self.value().take(),
            "square != mul self: a={:?}",
            a_val,
        );

        // distributivity: a * (b + 1) == a * b + a
        let b_plus_one = b.add(dr, &one);
        let lhs = a.mul(dr, &b_plus_one)?;
        let ab = a.mul(dr, &b)?;
        let rhs = ab.add(dr, &a);
        assert_eq!(
            *lhs.value().take(),
            *rhs.value().take(),
            "distributivity failed: a={:?} b={:?}",
            a_val,
            b_val,
        );

        // ------------------------------------------------------------------
        // Boolean identities
        // ------------------------------------------------------------------

        // double not
        let not_bv = bv.not(dr);
        let not_not_bv = not_bv.not(dr);
        assert_eq!(
            not_not_bv.value().take(),
            bv_val,
            "boolean double-not failed: bv={}",
            bv_val,
        );

        // self and
        let bv_and_bv = bv.and(dr, &bv)?;
        assert_eq!(
            bv_and_bv.value().take(),
            bv_val,
            "boolean self-and failed: bv={}",
            bv_val,
        );

        // ------------------------------------------------------------------
        // ConditionalSelect identities
        // ------------------------------------------------------------------

        let true_cond = Boolean::alloc(dr, allocator, witness.as_ref().map(|_| true))?;
        let false_cond = Boolean::alloc(dr, allocator, witness.as_ref().map(|_| false))?;

        // conditional_select formula: a + cond * (b - a)
        //   cond = false → a; cond = true → b.

        // false select returns the first arg
        let selected_false = false_cond.conditional_select(dr, &a, &b)?;
        assert_eq!(
            *selected_false.value().take(),
            a_val,
            "false-cond conditional_select failed: a={:?} b={:?}",
            a_val,
            b_val,
        );

        // true select returns the second arg
        let selected_true = true_cond.conditional_select(dr, &a, &b)?;
        assert_eq!(
            *selected_true.value().take(),
            b_val,
            "true-cond conditional_select failed: a={:?} b={:?}",
            a_val,
            b_val,
        );

        Ok(())
    });
});
