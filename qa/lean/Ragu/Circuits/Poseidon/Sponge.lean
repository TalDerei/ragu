import Clean.Circuit
import Ragu.Circuits.Poseidon.Permutation

/-!
# The Poseidon sponge

`poseidon.rs::Sponge` starts from the all-zero state (`Element::zero` per
word), buffers absorbed elements, and on the first `squeeze` adds the buffered
elements into the first `RATE` words (`state[i] = state[i].add(values[i])`,
virtual wires), runs the permutation, and returns `state[0]` (`get_rate`
reverses the rate words and `squeeze` pops the last).

`Hash1` is the single-block shape: `k ≤ RATE` absorbed elements and one
squeezed element, i.e. exactly one permutation.
-/

namespace Ragu.Circuits.Poseidon.Sponge
variable {p : ℕ} [Fact p.Prime] {t : ℕ} [NeZero t]

/-- The permutation's parameters: the MDS matrix and the round schedule. -/
structure Params (F : Type) (t : ℕ) where
  mds : Vector (Vector F t) t
  rounds : List (Permutation.RoundSpec F t)

/-- The schedule `poseidon.rs` runs: `full / 2` full rounds, `part` partial
rounds, `full / 2` full rounds, consuming the round constants in order. -/
def schedule (full part : ℕ) (rcs : Vector (Vector (F p) t) (full + part)) :
    List (Permutation.RoundSpec (F p) t) :=
  (List.finRange (full + part)).map fun i =>
    if i.val < full / 2 ∨ full / 2 + part ≤ i.val then .full rcs[i] else .part rcs[i]

/-- `Sponge::new` followed by absorbing `xs` and entering `squeeze`: the
zero state with `xs[i]` added into word `i`. -/
def initialState {k : ℕ} (xs : Vector (Expression (F p)) k) : Vector (Expression (F p)) t :=
  Vector.ofFn fun i => if h : i.val < k then (0 : Expression (F p)) + xs[i.val] else 0

def initialStateVal {k : ℕ} (xs : Vector (F p) k) : Vector (F p) t :=
  Vector.ofFn fun i => if h : i.val < k then xs[i.val] else 0

omit [NeZero t] in
theorem eval_initialState (env : Environment (F p)) {k : ℕ} (xs : Vector (Expression (F p)) k) :
    (initialState (t := t) xs).map (Expression.eval env) =
      initialStateVal (xs.map (Expression.eval env)) := by
  ext i hi
  simp only [initialState, initialStateVal, Vector.getElem_map, Vector.getElem_ofFn]
  split <;> simp [Expression.eval]

namespace Hash1

def main (P : Params (F p) t) (k : ℕ) (xs : Var (fields k) (F p)) :
    Circuit (F p) (Expression (F p)) := do
  let state ← Permutation.circuit P.mds P.rounds (initialState xs)
  pure (state[0]'(Nat.pos_of_neZero t))

def Assumptions {k : ℕ} (_xs : Vector (F p) k) := True

/-- The squeezed element is word `0` of the permuted initial state. -/
def Spec (P : Params (F p) t) {k : ℕ} (xs : Vector (F p) k) (out : F p) :=
  out = (Permutation.permuteVal P.mds P.rounds (initialStateVal xs))[0]'(Nat.pos_of_neZero t)

/-- A `def` rather than an `instance`: `t` is not determined by the instance
goal `ElaboratedCircuit (F p) (fields k) field`. -/
def elaborated (P : Params (F p) t) (k : ℕ) : ElaboratedCircuit (F p) (fields k) field where
  main := main P k
  localLength _ := Permutation.localLength P.rounds
  output xs offset := (Permutation.output P.mds P.rounds (initialState xs) offset)[0]'(Nat.pos_of_neZero t)
  localLength_eq xs offset := by
    simp [main, circuit_norm, Permutation.circuit]
  output_eq xs offset := by
    simp [main, circuit_norm, Permutation.circuit]
  subcircuitsConsistent xs offset := by
    simp [main, circuit_norm]

theorem soundness (P : Params (F p) t) (k : ℕ) :
    Soundness (F p) (elaborated P k) Assumptions (Spec P) := by
  circuit_proof_start [Permutation.circuit, Permutation.Assumptions, Permutation.Spec]
  rw [← h_input, ← eval_initialState, ← h_holds]
  simp [Vector.getElem_map]

theorem completeness (P : Params (F p) t) (k : ℕ) :
    Completeness (F p) (elaborated P k) Assumptions := by
  circuit_proof_start [Permutation.circuit, Permutation.Assumptions]

def circuit (P : Params (F p) t) (k : ℕ) : FormalCircuit (F p) (fields k) field :=
  { elaborated P k with
    Assumptions
    Spec := Spec P
    soundness := soundness P k
    completeness := completeness P k }

end Hash1

end Ragu.Circuits.Poseidon.Sponge
