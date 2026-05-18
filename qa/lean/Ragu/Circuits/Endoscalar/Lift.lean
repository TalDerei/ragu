import Clean.Circuit
import Ragu.Circuits.Boolean.And
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Endoscalar.Lift
variable {p : ℕ} [Fact p.Prime]

/-- `Endoscalar::lift` lifts a 128-bit endoscalar to its effective field-element
scalar. Implements Algorithm 2 from BGH19 (the Halo paper). Mirrors the Rust
loop in `crates/ragu_primitives/src/endoscalar.rs::lift`.

For each pair of bits (n, e):
  - `tmp = (n ? -1 : 1) · (e ? ζ : 1)`
  - `acc' = 2·acc + tmp`

Starting from `acc₀ = 2·(ζ+1)` and looping 64 times, output is `acc₆₄`.

The circuit-side `main` matches this by carrying `(circuit_acc, constant_term)`
where the invariant `eval(circuit_acc) + constant_term = native_acc` holds
each iteration. This Lean reimpl is monomorphic at 64 iterations; the
internal `(k : ℕ)` recursion is purely for proof shape (induction).

TODO: extraction instance deferred for the same reason as `Endoscalar.Alloc` —
the 256-op autogen (64 iterations × 4 ops per `Boolean.And` call) is too
large for current Clean simp/tactic infrastructure to reduce a
loop-based `main` against a literal flat list. Per fv-review's sub-gadget
carve-out, this is acceptable because `Endoscalar::lift` is only called from
`internal/endoscalar.rs` and `compute_v.rs`. -/

structure Input (F : Type) where
  bits : Vector F 128
deriving ProvableStruct

/-- One native Horner step. Given current accumulator and one 2-bit pair `(n, e)`
(interpreted as field 0 or 1), returns the next accumulator value. -/
def stepNative (ζ acc n e : F p) : F p :=
  let sign : F p := if n = 1 then -1 else 1
  let mult : F p := if e = 1 then ζ else 1
  2 * acc + sign * mult

/-- Iterate the native Horner step `k` times, starting at bit index `i`. -/
@[irreducible]
def liftNativeStep (ζ : F p) (bits : Vector (F p) 128) :
    (k : ℕ) → ℕ → F p → F p
  | 0, _, acc => acc
  | k+1, i, acc =>
    let n := if h : i < 128 then bits[i] else 0
    let e := if h : i + 1 < 128 then bits[i+1] else 0
    liftNativeStep ζ bits k (i + 2) (stepNative ζ acc n e)

/-- Native lift: 64-step Horner reduction starting from `2·(ζ+1)`. -/
def liftNative (ζ : F p) (bits : Vector (F p) 128) : F p :=
  liftNativeStep ζ bits 64 0 (2 * (ζ + 1))

/-- Per-iteration symbolic accumulator update (pure expression, no constraints). -/
def stepCircuit (ζ : F p) (n e ne acc : Expression (F p)) : Expression (F p) :=
  Expression.const 2 * acc +
    (Expression.const (-2) * n +
     Expression.const (ζ - 1) * e +
     Expression.const (2 * (1 - ζ)) * ne)

/-- Circuit-side recursive helper. After `k` iterations starting at bit index
`i`, returns `(acc, constant_term)`. Each iteration delegates to
`Boolean.And.circuit` for `n AND e`. Pure expression manipulation otherwise.

Marked `@[irreducible]` so the elaborator doesn't eagerly unfold all 64
iterations when `main` calls `liftStep curveParams.ζ input.bits 64 ...`.
Proofs unfold it explicitly via `simp only [liftStep]` or via induction. -/
def liftStep (ζ : F p) (bits : Vector (Expression (F p)) 128) :
    (k : ℕ) → ℕ → Expression (F p) → F p → Circuit (F p) (Expression (F p) × F p)
  | 0, _, acc, ct => pure (acc, ct)
  | k+1, i, acc, ct => do
    let n_var := if h : i < 128 then bits[i] else 0
    let e_var := if h : i + 1 < 128 then bits[i+1] else 0
    let ne ← Boolean.And.circuit ⟨n_var, e_var⟩
    liftStep ζ bits k (i + 2) (stepCircuit ζ n_var e_var ne acc) (2 * ct + 1)

def main (curveParams : Point.Spec.CurveParams p) (input : Var Input (F p))
    : Circuit (F p) (Expression (F p)) := do
  let (acc, ct) ← liftStep curveParams.ζ input.bits 64 0
    (Expression.const 0) (2 * (curveParams.ζ + 1))
  return acc + Expression.const ct

def Assumptions (_curveParams : Point.Spec.CurveParams p) (input : Input (F p)) :=
  ∀ i : Fin 128, IsBool input.bits[i]

def Spec (curveParams : Point.Spec.CurveParams p) (input : Input (F p)) (out : F p) :=
  out = liftNative curveParams.ζ input.bits

/-- `liftStep ζ bits k i acc ct` has local length `3 * k` (one `Boolean.And.circuit`
of length 3 per iteration). -/
private lemma liftStep_localLength (ζ : F p) (bits : Vector (Expression (F p)) 128)
    (k i : ℕ) (acc : Expression (F p)) (ct : F p) (offset : ℕ) :
    Operations.localLength (liftStep ζ bits k i acc ct offset).2 = 3 * k := by
  induction k generalizing i acc ct offset with
  | zero => rfl
  | succ k ih =>
    simp only [liftStep, Circuit.bind_def, circuit_norm,
      Boolean.And.circuit, Boolean.And.elaborated, Boolean.And.main]
    rw [ih]
    ring

/-- `liftStep` produces subcircuit-consistent operations. -/
private lemma liftStep_subcircuitsConsistent (ζ : F p) (bits : Vector (Expression (F p)) 128)
    (k i : ℕ) (acc : Expression (F p)) (ct : F p) (offset : ℕ) :
    Operations.forAll offset
      { subcircuit := fun off {m} _ => m = off }
      (liftStep ζ bits k i acc ct offset).2 := by
  induction k generalizing i acc ct offset with
  | zero => simp [liftStep, circuit_norm]
  | succ k ih =>
    simp only [liftStep, Circuit.bind_def, circuit_norm,
      Boolean.And.circuit, Boolean.And.elaborated, Boolean.And.main]
    rw [show (3 + offset : ℕ) = offset + 3 from Nat.add_comm 3 offset]
    exact ih _ _ _ (offset + 3)

instance elaborated (curveParams : Point.Spec.CurveParams p)
    : ElaboratedCircuit (F p) Input field where
  main := main curveParams
  localLength _ := 64 * 3
  localLength_eq input offset := by
    simp only [main, Circuit.bind_def, circuit_norm]
    exact liftStep_localLength _ _ _ _ _ _ _
  subcircuitsConsistent input offset := by
    simp only [main, Circuit.bind_def, circuit_norm]
    exact liftStep_subcircuitsConsistent _ _ _ _ _ _ _

/-- Algebraic identity per fv-review's "reusable building blocks": for
`n, e ∈ {0, 1}`, `1 + (-2·n + (ζ-1)·e + 2·(1-ζ)·n·e) = (if n=1 then -1 else 1) · (if e=1 then ζ else 1)`. -/
private lemma step_identity (ζ n e : F p) (hn : IsBool n) (he : IsBool e) :
    1 + (-2 * n + (ζ - 1) * e + 2 * (1 - ζ) * (n * e)) =
    (if n = 1 then -1 else 1) * (if e = 1 then ζ else 1) := by
  rcases hn with hn | hn <;> rcases he with he | he <;>
    simp [hn, he] <;> ring

/-- The invariant connecting circuit-side `(acc, ct)` to native `liftNativeStep`.
After `k` iterations starting at bit index `i`, given the constraints hold,
`eval(acc) + ct = liftNativeStep ζ bits_val k i (initial_acc_val + initial_ct)`. -/
private lemma liftStep_eval_correct (ζ : F p) (env : Environment (F p))
    (bits_var : Vector (Expression (F p)) 128) (bits_val : Vector (F p) 128)
    (h_bits : ∀ j : Fin 128, Expression.eval env bits_var[j] = bits_val[j])
    (h_isBool : ∀ j : Fin 128, IsBool bits_val[j]) :
    ∀ (k i : ℕ) (_h_i : i + 2 * k ≤ 128)
      (acc_var : Expression (F p)) (acc_val ct : F p) (offset : ℕ),
      Expression.eval env acc_var = acc_val →
      Circuit.ConstraintsHold.Soundness env (liftStep ζ bits_var k i acc_var ct offset).2 →
      Expression.eval env (liftStep ζ bits_var k i acc_var ct offset).1.1 +
        (liftStep ζ bits_var k i acc_var ct offset).1.2 =
      liftNativeStep ζ bits_val k i (acc_val + ct) := by
  intro k
  induction k with
  | zero =>
    intros i _ acc_var acc_val ct offset h_acc _
    unfold liftStep liftNativeStep
    simp [h_acc]
  | succ k ih =>
    intros i h_i acc_var acc_val ct offset h_acc h_sound
    have hi : i < 128 := by omega
    have hi1 : i + 1 < 128 := by omega
    have h_i' : (i + 2) + 2 * k ≤ 128 := by omega
    have h_n_eval : Expression.eval env bits_var[i] = bits_val[i] := h_bits ⟨i, hi⟩
    have h_e_eval : Expression.eval env bits_var[i+1] = bits_val[i+1] := h_bits ⟨i+1, hi1⟩
    have h_n_bool : IsBool bits_val[i] := h_isBool ⟨i, hi⟩
    have h_e_bool : IsBool bits_val[i+1] := h_isBool ⟨i+1, hi1⟩
    -- Unfold liftStep one level (with the if-then-else's `then` branch chosen).
    -- Boolean.And's subcircuit gives us its Spec: ne.val = n.val &&& e.val ∧ IsBool ne.
    simp only [liftStep, Circuit.bind_def, circuit_norm,
      Boolean.And.circuit, Boolean.And.elaborated, Boolean.And.main,
      Boolean.And.Assumptions, Boolean.And.Spec, dif_pos hi, dif_pos hi1] at h_sound ⊢
    -- Decompose h_sound into Boolean.And's spec consequence and the rest's soundness.
    -- The exact shape depends on circuit_norm's simplification — we attempt the
    -- common pattern from squareIter_eval_correct.
    obtain ⟨h_and, h_rest⟩ := h_sound
    -- Boolean.And.Spec gives us (out.val = a.val &&& b.val ∧ IsBool out)
    -- For a, b ∈ {0,1}, this means out = a * b in the field.
    have h_ne_val : Expression.eval env (var ⟨offset + 2⟩) =
        bits_val[i] * bits_val[i+1] := by
      have h := h_and ⟨h_isBool ⟨i, hi⟩, h_isBool ⟨i+1, hi1⟩⟩
      rcases h_isBool ⟨i, hi⟩ with hn | hn <;>
        rcases h_isBool ⟨i+1, hi1⟩ with he | he <;>
        simp_all [Expression.eval, IsBool.and_eq_val_and, IsBool] <;>
        ring
    -- Now apply IH with the new acc/ct/offset
    have h_new_acc : Expression.eval env
        (stepCircuit ζ bits_var[i] bits_var[i+1] (var ⟨offset + 2⟩) acc_var) =
        2 * acc_val + (-2 * bits_val[i] + (ζ - 1) * bits_val[i+1] +
          2 * (1 - ζ) * (bits_val[i] * bits_val[i+1])) := by
      simp [stepCircuit, Expression.eval, h_acc,
        h_bits ⟨i, hi⟩, h_bits ⟨i+1, hi1⟩, h_ne_val]
      ring
    rw [ih (i + 2) h_i' _ _ (2 * ct + 1) (offset + 3) h_new_acc h_rest]
    -- Unfold liftNativeStep at (k+1)
    unfold liftNativeStep
    simp only [dif_pos hi, dif_pos hi1, stepNative]
    -- Use step_identity to bridge the two sides
    have h_id := step_identity ζ bits_val[i] bits_val[i+1]
      (h_isBool ⟨i, hi⟩) (h_isBool ⟨i+1, hi1⟩)
    -- Need: 2*acc_val + 2*ct + 1 + (...) = 2*(acc_val + ct) + sign*mult
    linear_combination h_id

theorem soundness (curveParams : Point.Spec.CurveParams p)
    : Soundness (F p) (elaborated curveParams) (Assumptions curveParams)
        (Spec curveParams) := by
  circuit_proof_start [Boolean.And.circuit, Boolean.And.Assumptions, Boolean.And.Spec]
  -- h_input gives per-field equalities
  have h_bits_eq : ∀ j : Fin 128, Expression.eval env input_var.bits[j] = input.bits[j] := by
    intro j
    have : (eval env input_var).bits[j] = input.bits[j] := by rw [h_input]
    simpa using this
  -- Apply the invariant
  have h_inv := liftStep_eval_correct curveParams.ζ env input_var.bits input.bits
    h_bits_eq h_assumptions 64 0 (by omega)
    (Expression.const 0) 0 (2 * (curveParams.ζ + 1)) i₀
    (by simp [Expression.eval]) h_holds
  -- Conclude: output = eval(acc + Expression.const ct) = eval(acc) + ct = liftNativeStep
  simp only [main, Circuit.bind_def, circuit_norm, Spec, liftNative]
  rw [show (0 + 2 * (curveParams.ζ + 1) : F p) = 2 * (curveParams.ζ + 1) by ring]
  simp only [Expression.eval]
  linear_combination h_inv

theorem completeness (curveParams : Point.Spec.CurveParams p)
    : Completeness (F p) (elaborated curveParams) (Assumptions curveParams) := by
  circuit_proof_start [Boolean.And.circuit, Boolean.And.Assumptions, Boolean.And.Spec]
  -- The Boolean.And calls have ProverAssumptions = True (per Boolean.And.lean)
  -- so completeness should follow from circuit_proof_start's automation
  -- plus the IsBool assumptions on each bit.
  simp_all [main, liftStep, circuit_norm]

def circuit (curveParams : Point.Spec.CurveParams p) : FormalCircuit (F p) Input field :=
  { elaborated curveParams with
    Assumptions := Assumptions curveParams
    Spec := Spec curveParams
    soundness := soundness curveParams
    completeness := completeness curveParams }

end Ragu.Circuits.Endoscalar.Lift
