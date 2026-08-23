import Clean.Circuit
import Clean.Circuit.Loops
import Ragu.Circuits.Poseidon.Sbox
import Ragu.Circuits.Poseidon.Linear

/-!
# One Poseidon round

`poseidon.rs::Permutation::execute` runs, per round,

1. `add_round_constants`: `state[i] += rc[i]` (a virtual wire each),
2. `sbox` on the first `elems` words (`elems = T` in a full round, `1` in a
   partial round): three `Element::mul` gates per word,
3. `mds`: every new word is a `multiadd` of the old ones (virtual wires).

The output words are passed through `Linear.normalizeLinear` so that the
partial rounds' linear words stay small expressions (see `Linear.lean`);
this is invisible to both the constraint system and the fingerprint.
-/

namespace Ragu.Circuits.Poseidon.Round
variable {p : ℕ} [Fact p.Prime]

section Linear
variable {t : ℕ}

/-- `Σᵢ coeffs[i] · xs[i]`, left-nested, mirroring `multiadd`'s accumulator. -/
def linComb (coeffs : Vector (F p) t) (xs : Vector (Expression (F p)) t) : Expression (F p) :=
  Fin.foldl t (fun acc i => acc + Expression.const coeffs[i] * xs[i]) 0

/-- Value-level `linComb`. -/
def linCombVal (coeffs : Vector (F p) t) (xs : Vector (F p) t) : F p :=
  Fin.foldl t (fun acc i => acc + coeffs[i] * xs[i]) 0

theorem eval_foldl_linear (env : Environment (F p)) (n : ℕ) (c : Fin n → F p)
    (x : Fin n → Expression (F p)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + Expression.const (c i) * x i) 0) =
      Fin.foldl n (fun acc i => acc + c i * Expression.eval env (x i)) 0 := by
  induction n with
  | zero => simp [Expression.eval]
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    simp only [Expression.eval]
    congr 1
    exact ih _ _

theorem eval_linComb (env : Environment (F p)) (coeffs : Vector (F p) t)
    (xs : Vector (Expression (F p)) t) :
    Expression.eval env (linComb coeffs xs) = linCombVal coeffs (xs.map (Expression.eval env)) := by
  unfold linComb linCombVal
  rw [eval_foldl_linear]
  simp [Vector.getElem_map]

/-- `add_round_constants`. -/
def addConstants (rc : Vector (F p) t) (xs : Vector (Expression (F p)) t) :
    Vector (Expression (F p)) t :=
  Vector.ofFn fun i => xs[i] + Expression.const rc[i]

def addConstantsVal (rc : Vector (F p) t) (xs : Vector (F p) t) : Vector (F p) t :=
  Vector.ofFn fun i => xs[i] + rc[i]

/-- `mds`: row `j` of the matrix dotted with the state. -/
def applyMds (mds : Vector (Vector (F p) t) t) (xs : Vector (Expression (F p)) t) :
    Vector (Expression (F p)) t :=
  Vector.ofFn fun j => Linear.normalizeLinear (linComb mds[j] xs)

def applyMdsVal (mds : Vector (Vector (F p) t) t) (xs : Vector (F p) t) : Vector (F p) t :=
  Vector.ofFn fun j => linCombVal mds[j] xs

theorem eval_addConstants (env : Environment (F p)) (rc : Vector (F p) t)
    (xs : Vector (Expression (F p)) t) :
    (addConstants rc xs).map (Expression.eval env) = addConstantsVal rc (xs.map (Expression.eval env)) := by
  ext i hi
  simp [addConstants, addConstantsVal, Expression.eval]

theorem eval_applyMds (env : Environment (F p)) (mds : Vector (Vector (F p) t) t)
    (xs : Vector (Expression (F p)) t) :
    (applyMds mds xs).map (Expression.eval env) = applyMdsVal mds (xs.map (Expression.eval env)) := by
  ext j hj
  simp [applyMds, applyMdsVal, Linear.eval_normalizeLinear, eval_linComb]

end Linear

/-- Per-round data: the MDS matrix (shared by every round) and this round's
constants. -/
structure Params (F : Type) (t : ℕ) where
  mds : Vector (Vector F t) t
  rc : Vector F t

/-- The S-box applied to every word: a full round's nonlinear layer. -/
def sboxAllVal {t : ℕ} (xs : Vector (F p) t) : Vector (F p) t :=
  xs.map (· ^ 5)

/-- The S-box applied to word `0` only: a partial round's nonlinear layer. -/
def sboxFirstVal {t : ℕ} [NeZero t] (xs : Vector (F p) t) : Vector (F p) t :=
  xs.set 0 (xs[0]'(Nat.pos_of_neZero t) ^ 5) (Nat.pos_of_neZero t)

namespace Full
variable {t : ℕ}

def main (P : Params (F p) t) (state : Vector (Expression (F p)) t) :
    Circuit (F p) (Vector (Expression (F p)) t) := do
  let state := addConstants P.rc state
  let state ← Circuit.map state Sbox.circuit
  pure (applyMds P.mds state)

def Assumptions (_state : Vector (F p) t) := True

def Spec (P : Params (F p) t) (state : Vector (F p) t) (out : Vector (F p) t) :=
  out = applyMdsVal P.mds (sboxAllVal (addConstantsVal P.rc state))

instance elaborated (P : Params (F p) t) : ElaboratedCircuit (F p) (fields t) (fields t) where
  main := main P
  localLength _ := 9 * t
  localLength_eq state offset := by
    simp +arith [main, circuit_norm, Sbox.circuit]
  subcircuitsConsistent state offset := by
    simp [main, circuit_norm]

theorem soundness (P : Params (F p) t) :
    Soundness (F p) (elaborated P) Assumptions (Spec P) := by
  circuit_proof_start [Sbox.circuit, Sbox.Assumptions, Sbox.Spec]
  rw [eval_applyMds]
  congr 1
  rw [← h_input, ← eval_addConstants]
  ext i hi
  simp only [Vector.getElem_map, Vector.getElem_mapIdx, sboxAllVal, Expression.eval]
  exact h_holds ⟨i, hi⟩

theorem completeness (P : Params (F p) t) :
    Completeness (F p) (elaborated P) Assumptions := by
  circuit_proof_start [Sbox.circuit, Sbox.Assumptions]

def circuit (P : Params (F p) t) : FormalCircuit (F p) (fields t) (fields t) :=
  { elaborated P with
    Assumptions
    Spec := Spec P
    soundness := soundness P
    completeness := completeness P }

end Full

namespace Partial
variable {t : ℕ} [NeZero t]

def main (P : Params (F p) t) (state : Vector (Expression (F p)) t) :
    Circuit (F p) (Vector (Expression (F p)) t) := do
  let state := addConstants P.rc state
  let y ← Sbox.circuit (state[0]'(Nat.pos_of_neZero t))
  pure (applyMds P.mds (state.set 0 y (Nat.pos_of_neZero t)))

def Assumptions (_state : Vector (F p) t) := True

def Spec (P : Params (F p) t) (state : Vector (F p) t) (out : Vector (F p) t) :=
  out = applyMdsVal P.mds (sboxFirstVal (addConstantsVal P.rc state))

instance elaborated (P : Params (F p) t) : ElaboratedCircuit (F p) (fields t) (fields t) where
  main := main P
  localLength _ := 9
  output state offset :=
    applyMds P.mds ((addConstants P.rc state).set 0 (varFromOffset field (offset + 8))
      (Nat.pos_of_neZero t))
  localLength_eq state offset := by
    simp +arith [main, circuit_norm, Sbox.circuit]
  subcircuitsConsistent state offset := by
    simp [main, circuit_norm]
  output_eq state offset := by
    simp [main, circuit_norm, Sbox.circuit]

theorem soundness (P : Params (F p) t) :
    Soundness (F p) (elaborated P) Assumptions (Spec P) := by
  circuit_proof_start [Sbox.circuit, Sbox.Assumptions, Sbox.Spec]
  rw [eval_applyMds]
  congr 1
  rw [← h_input, ← eval_addConstants]
  ext i hi
  simp only [Vector.getElem_map, Vector.getElem_set, sboxFirstVal]
  split
  · rename_i h
    subst h
    simp only [Expression.eval]
    exact h_holds
  · rfl

theorem completeness (P : Params (F p) t) :
    Completeness (F p) (elaborated P) Assumptions := by
  circuit_proof_start [Sbox.circuit, Sbox.Assumptions]

def circuit (P : Params (F p) t) : FormalCircuit (F p) (fields t) (fields t) :=
  { elaborated P with
    Assumptions
    Spec := Spec P
    soundness := soundness P
    completeness := completeness P }

end Partial

end Ragu.Circuits.Poseidon.Round
