//! Fuzz three-way s(X,Y) polynomial agreement.
//!
//! Three completely independent Driver implementations evaluate the same
//! circuit's wiring polynomial:
//!   - sxy::eval  → scalar s(x, y)
//!   - sx::eval   → unstructured polynomial s(x, Y), then eval at y
//!   - sy::eval   → structured polynomial s(X, y), then eval at x
//!
//! Each uses a different wire representation and accumulation strategy.
//! The sy evaluator uses RefCell-based virtual wires with a free list.
//! All three must agree for any circuit shape and any evaluation point.
//!
//! Invariant: sxy(x, y) == sx(x).eval(y) == sy(y).eval(x)

#![no_main]

use arbitrary::Arbitrary;
use ff::Field;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_circuits::{
    CircuitExt,
    floor_planner::floor_plan,
    polynomials::TestRank,
    registry::Key,
};
use ragu_testing::circuits::SquareCircuit;

#[derive(Arbitrary, Debug)]
struct Input {
    /// Number of squarings (clamped to 1..=120 to stay within TestRank)
    times: u8,
    /// Evaluation point seeds
    x_seed: u64,
    y_seed: u64,
    /// Registry key seed
    key_seed: u64,
}

fuzz_target!(|input: Input| {
    // Clamp times to stay within TestRank bounds (n = 2^7 = 128 muls max)
    let times = ((input.times as usize) % 120).max(1);

    let circuit = SquareCircuit { times };
    let obj = match circuit.into_object::<TestRank>() {
        Ok(obj) => obj,
        Err(_) => return, // Circuit too large for rank — skip
    };

    let plan = floor_plan(obj.segment_records());
    // Key::new requires a non-zero element (it computes the inverse).
    if input.key_seed == 0 {
        return;
    }
    let key = Key::new(Fp::from(input.key_seed));
    let x = Fp::from(input.x_seed);
    let y = Fp::from(input.y_seed);

    // Three independent evaluations
    let sxy = obj.sxy(x, y, &key, &plan);
    let sx_at_y = obj.sx(x, &key, &plan).eval(y);
    let sy_at_x = obj.sy(y, &key, &plan).eval(x);

    assert_eq!(sxy, sx_at_y, "sxy != sx(x).eval(y) for times={times}");
    assert_eq!(sxy, sy_at_x, "sxy != sy(y).eval(x) for times={times}");
});
