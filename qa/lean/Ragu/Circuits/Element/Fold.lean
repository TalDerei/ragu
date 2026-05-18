import Clean.Circuit
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Element.Fold
variable {p : ℕ} [Fact p.Prime]

/-- `Element::fold` is a variadic Horner reduction in Rust: given
elements `[x₀, x₁, …, x_{n-1}]` and a scale factor `s`, returns
`((…((x₀·s + x₁)·s + x₂)…)·s + x_{n-1})`, with the empty-input case
returning zero. This Lean reimpl is polymorphic on `n : ℕ`, mirroring
the Rust gadget's full generality. -/
structure Input (n : ℕ) (F : Type) where
  xs : Vector F n
  s : F
deriving ProvableStruct

/-- Horner reduction step: given an accumulator and a vector of `m`
remaining elements, produces the final accumulator after `m` Mul-then-add
iterations. Each iteration calls `Mul.circuit`, matching the autogen's
per-step shape of one witness-3 + three asserts. -/
def hornerStep :
    (m : ℕ) → Expression (F p) → Vector (Expression (F p)) m → Expression (F p) →
      Circuit (F p) (Expression (F p))
  | 0, acc, _, _ => pure acc
  | m+1, acc, rest, s => do
    let scaled ← Mul.circuit ⟨acc, s⟩
    hornerStep m (scaled + rest[0]) rest.tail s

def main : (n : ℕ) → Var (Input n) (F p) → Circuit (F p) (Expression (F p))
  | 0, _ => pure 0
  | _+1, input => hornerStep _ input.xs[0] input.xs.tail input.s

/-- Native (no-circuit) Horner reduction, mirrors `hornerStep`. -/
def hornerVal : (m : ℕ) → F p → Vector (F p) m → F p → F p
  | 0, acc, _, _ => acc
  | m+1, acc, rest, s => hornerVal m (acc * s + rest[0]) rest.tail s

def Assumptions {n : ℕ} (_input : Input n (F p)) := True

/-- For `n = 0` the output is `0` (matching `Element::zero`).
For `n ≥ 1` the output is the Horner reduction of `xs` with scale `s`. -/
def Spec {n : ℕ} (input : Input n (F p)) (output : F p) :=
  output = match n, input.xs with
    | 0, _ => 0
    | _+1, xs => hornerVal _ xs[0] xs.tail input.s

/-- `hornerStep m acc rest s` has local length `3 * m` (one `Mul.circuit`
of length 3 per iteration), for any accumulator, remaining vector, and
starting offset. -/
private lemma hornerStep_localLength (m : ℕ) (acc : Expression (F p))
    (rest : Vector (Expression (F p)) m) (s : Expression (F p)) (n : ℕ) :
    Operations.localLength (hornerStep m acc rest s n).2 = 3 * m := by
  induction m generalizing acc s n with
  | zero => rfl
  | succ m ih =>
    simp only [hornerStep, Circuit.bind_def, circuit_norm, Mul.circuit, Mul.elaborated]
    rw [ih]
    ring

/-- `hornerStep m acc rest s` produces subcircuit-consistent operations. -/
private lemma hornerStep_subcircuitsConsistent (m : ℕ) (acc : Expression (F p))
    (rest : Vector (Expression (F p)) m) (s : Expression (F p)) (n : ℕ) :
    Operations.forAll n
      { subcircuit := fun offset {k} _ => k = offset }
      (hornerStep m acc rest s n).2 := by
  induction m generalizing acc s n with
  | zero => simp [hornerStep, circuit_norm]
  | succ m ih =>
    simp only [hornerStep, Circuit.bind_def, circuit_norm, Mul.circuit, Mul.elaborated]
    rw [show (3 + n : ℕ) = n + 3 from Nat.add_comm 3 n]
    exact ih _ _ _ (n + 3)

instance elaborated (n : ℕ) : ElaboratedCircuit (F p) (Input n) field where
  main := main n
  localLength _ := 3 * (n - 1)
  localLength_eq input offset := by
    rcases n with _ | n
    · simp [main, circuit_norm]
    · simp only [main, circuit_norm]
      exact hornerStep_localLength n _ _ _ _
  subcircuitsConsistent input offset := by
    rcases n with _ | n
    · simp [main, circuit_norm]
    · simp only [main, circuit_norm]
      exact hornerStep_subcircuitsConsistent n _ _ _ _

/-- `(map f v).tail = map f v.tail`. -/
private lemma Vector.map_tail {α β : Type*} {n : ℕ} (f : α → β) (v : Vector α (n+1)) :
    (v.map f).tail = v.tail.map f := by
  apply Vector.ext
  intros i hi
  simp

/-- The output of `hornerStep m acc_var rest_var s_var` evaluates to
`hornerVal m acc_val rest_val s_val` (where rest_val / s_val / acc_val
are the evaluations of the corresponding expression args), provided the
Mul constraints from each iteration are satisfied. Proved by induction
on `m`, delegating each step's product equality to `Mul.Spec`. -/
private lemma hornerStep_eval_correct (m : ℕ) (env : Environment (F p))
    (acc_var : Expression (F p)) (acc_val : F p)
    (rest_var : Vector (Expression (F p)) m)
    (s_var : Expression (F p)) (s_val : F p) (n : ℕ)
    (h_acc : Expression.eval env acc_var = acc_val)
    (h_s : Expression.eval env s_var = s_val)
    (h_sound : Circuit.ConstraintsHold.Soundness env (hornerStep m acc_var rest_var s_var n).2) :
    Expression.eval env (hornerStep m acc_var rest_var s_var n).1
      = hornerVal m acc_val (rest_var.map (Expression.eval env)) s_val := by
  induction m generalizing acc_var acc_val s_var s_val n with
  | zero =>
    simp only [hornerStep, hornerVal, circuit_norm]
    exact h_acc
  | succ m ih =>
    simp only [hornerStep, Circuit.bind_def, circuit_norm,
      Mul.circuit, Mul.Assumptions, Mul.Spec, Mul.elaborated] at h_sound ⊢
    obtain ⟨h_mul, h_rest⟩ := h_sound
    have h_new_acc : Expression.eval env (var ⟨n + 2⟩ + rest_var[0])
        = acc_val * s_val + Expression.eval env rest_var[0] := by
      simp [Expression.eval, h_mul, h_acc, h_s]
    rw [ih (var ⟨n + 2⟩ + rest_var[0]) (acc_val * s_val + Expression.eval env rest_var[0])
        rest_var.tail s_var s_val (n + 3) h_new_acc h_s h_rest]
    -- Goal: hornerVal m (acc_val * s_val + eval rest_var[0]) (map eval rest_var.tail) s_val
    --     = hornerVal (m + 1) acc_val (map eval rest_var) s_val
    -- RHS unfolds (via hornerVal definition for m+1):
    --   = hornerVal m (acc_val * s_val + (map eval rest_var)[0]) (map eval rest_var).tail s_val
    show _ = hornerVal (m + 1) acc_val (Vector.map (Expression.eval env) rest_var) s_val
    rw [hornerVal]
    congr 1
    · simp [Vector.getElem_map]
    · apply Vector.ext
      intro i hi
      simp [Vector.getElem_map]

theorem soundness (n : ℕ) :
    Soundness (F p) (elaborated n) Assumptions Spec := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions, Mul.Spec]
  rcases n with _ | n
  · -- n = 0: main returns pure 0, output = 0, Spec is `output = 0`
    simp [circuit_norm] at h_holds ⊢
  · -- n = n'+1: main = hornerStep n' xs[0] xs.tail s
    simp only [circuit_norm] at h_holds ⊢
    have h_eval := hornerStep_eval_correct n env
      input_var.xs[0] (Expression.eval env input_var.xs[0])
      input_var.xs.tail input_var.s (Expression.eval env input_var.s) i₀
      rfl rfl h_holds
    -- Decompose h_input into per-field equalities
    have h_xs : input.xs = Vector.map (Expression.eval env) input_var.xs := by
      rw [← h_input]
    have h_s : input.s = Expression.eval env input_var.s := by
      rw [← h_input]
    -- Unfold Spec for the n+1 branch
    show Expression.eval env _ = hornerVal n input.xs[0] input.xs.tail input.s
    rw [h_xs, h_s, Vector.getElem_map, Vector.map_tail]
    exact h_eval

/-- Companion to `hornerStep_eval_correct` for the completeness side:
given that the prover environment uses the canonical local witnesses for
`hornerStep`, the Mul constraints all hold by construction. -/
private lemma hornerStep_completeness (m : ℕ) (env : ProverEnvironment (F p))
    (acc_var : Expression (F p)) (acc_val : F p)
    (rest_var : Vector (Expression (F p)) m)
    (s_var : Expression (F p)) (s_val : F p) (n : ℕ)
    (h_acc : Expression.eval env.toEnvironment acc_var = acc_val)
    (h_s : Expression.eval env.toEnvironment s_var = s_val)
    (h_env : env.UsesLocalWitnessesCompleteness n (hornerStep m acc_var rest_var s_var n).2) :
    Circuit.ConstraintsHold.Completeness env (hornerStep m acc_var rest_var s_var n).2 := by
  induction m generalizing acc_var acc_val s_var s_val n with
  | zero =>
    simp [hornerStep, circuit_norm]
  | succ m ih =>
    simp only [hornerStep, Circuit.bind_def, circuit_norm,
      Mul.circuit, Mul.Assumptions, Mul.Spec, Mul.elaborated] at h_env ⊢
    obtain ⟨h_wit, h_rest⟩ := h_env
    have h_new_acc : Expression.eval env.toEnvironment (var ⟨n + 2⟩ + rest_var[0])
        = acc_val * s_val + Expression.eval env.toEnvironment rest_var[0] := by
      simp [Expression.eval, h_wit, h_acc, h_s]
    exact ih (var ⟨n + 2⟩ + rest_var[0]) _ rest_var.tail s_var s_val (n + 3) h_new_acc h_s h_rest

theorem completeness (n : ℕ) :
    Completeness (F p) (elaborated n) Assumptions := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions, Mul.Spec]
  rcases n with _ | n
  · simp [circuit_norm]
  · simp only [circuit_norm] at h_env ⊢
    exact hornerStep_completeness n env
      input_var.xs[0] (Expression.eval env.toEnvironment input_var.xs[0])
      input_var.xs.tail input_var.s (Expression.eval env.toEnvironment input_var.s) i₀
      rfl rfl h_env

def circuit (n : ℕ) : FormalCircuit (F p) (Input n) field :=
  { elaborated n with
    Assumptions
    Spec
    soundness := soundness n
    completeness := completeness n }

end Ragu.Circuits.Element.Fold
