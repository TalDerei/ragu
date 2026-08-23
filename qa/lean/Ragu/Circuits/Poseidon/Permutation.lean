import Clean.Circuit
import Ragu.Circuits.Poseidon.Round

/-!
# The Poseidon permutation

`poseidon.rs::Permutation::execute` runs a fixed schedule of rounds:
`FULL_ROUNDS / 2` full rounds, `PARTIAL_ROUNDS` partial rounds, and
`FULL_ROUNDS / 2` full rounds again, each with its own round constants. The
reimplementation takes the schedule as a list of `RoundSpec`s and recurses
over it: every round is the boxed `Round.Full` / `Round.Partial` sub-circuit
and the tail is the recursive circuit, so soundness and completeness are
proved once by induction on the list.

`Circuit.foldl` is not usable here because it demands `ConstantOutput`, and a
round's output words are linear in its input words.
-/

namespace Ragu.Circuits.Poseidon.Permutation
variable {p : ℕ} [Fact p.Prime] {t : ℕ} [NeZero t]

/-- One entry of the round schedule: which nonlinear layer to apply (`full`:
every word, `part`: word `0` only — `partial` is a Lean keyword), and the
round's constants. -/
inductive RoundSpec (F : Type) (t : ℕ)
  | full (rc : Vector F t)
  | part (rc : Vector F t)

/-- Value-level round function. -/
def roundVal (mds : Vector (Vector (F p) t) t) : RoundSpec (F p) t → Vector (F p) t → Vector (F p) t
  | .full rc, s => Round.applyMdsVal mds (Round.sboxAllVal (Round.addConstantsVal rc s))
  | .part rc, s => Round.applyMdsVal mds (Round.sboxFirstVal (Round.addConstantsVal rc s))

/-- Value-level permutation: the rounds applied in schedule order. -/
def permuteVal (mds : Vector (Vector (F p) t) t) : List (RoundSpec (F p) t) → Vector (F p) t → Vector (F p) t
  | [], s => s
  | r :: rs, s => permuteVal mds rs (roundVal mds r s)

/-! A single round of either kind, boxed as one sub-circuit so that the
schedule recursion below is uniform in the round kind. -/
namespace AnyRound

def main (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t)
    (state : Var (fields t) (F p)) : Circuit (F p) (Var (fields t) (F p)) :=
  match r with
  | .full rc => Round.Full.circuit ⟨mds, rc⟩ state
  | .part rc => Round.Partial.circuit ⟨mds, rc⟩ state

def localLength : RoundSpec (F p) t → ℕ
  | .full _ => 9 * t
  | .part _ => 9

def output (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t)
    (state : Var (fields t) (F p)) (offset : ℕ) : Var (fields t) (F p) :=
  match r with
  | .full rc => (Round.Full.circuit ⟨mds, rc⟩).output state offset
  | .part rc => (Round.Partial.circuit ⟨mds, rc⟩).output state offset

def Assumptions (_state : Vector (F p) t) := True

def Spec (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t)
    (state : Vector (F p) t) (out : Vector (F p) t) :=
  out = roundVal mds r state

instance elaborated (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t) :
    ElaboratedCircuit (F p) (fields t) (fields t) where
  main := main mds r
  localLength _ := localLength r
  output := output mds r
  localLength_eq state offset := by
    cases r <;> simp [main, localLength, circuit_norm, Round.Full.circuit, Round.Partial.circuit]
  output_eq state offset := by
    cases r <;> simp [main, output, circuit_norm]
  subcircuitsConsistent state offset := by
    cases r <;> simp [main, circuit_norm]

theorem soundness (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t) :
    Soundness (F p) (elaborated mds r) Assumptions (Spec mds r) := by
  cases r with
  | full rc =>
    circuit_proof_start [Round.Full.circuit, Round.Full.Assumptions, Round.Full.Spec]
    exact h_holds
  | part rc =>
    circuit_proof_start [Round.Partial.circuit, Round.Partial.Assumptions, Round.Partial.Spec]
    exact h_holds

theorem completeness (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t) :
    Completeness (F p) (elaborated mds r) Assumptions := by
  cases r with
  | full rc =>
    circuit_proof_start [Round.Full.circuit, Round.Full.Assumptions]
  | part rc =>
    circuit_proof_start [Round.Partial.circuit, Round.Partial.Assumptions]

def circuit (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t) :
    FormalCircuit (F p) (fields t) (fields t) :=
  { elaborated mds r with
    Assumptions
    Spec := Spec mds r
    soundness := soundness mds r
    completeness := completeness mds r }

end AnyRound

def main (mds : Vector (Vector (F p) t) t) :
    List (RoundSpec (F p) t) → Var (fields t) (F p) → Circuit (F p) (Var (fields t) (F p))
  | [], state => pure state
  | r :: rs, state => do
    let state ← AnyRound.circuit mds r state
    main mds rs state

def localLength : List (RoundSpec (F p) t) → ℕ
  | [] => 0
  | r :: rs => AnyRound.localLength r + localLength rs

def output (mds : Vector (Vector (F p) t) t) :
    List (RoundSpec (F p) t) → Var (fields t) (F p) → ℕ → Var (fields t) (F p)
  | [], state, _ => state
  | r :: rs, state, offset =>
    output mds rs (AnyRound.output mds r state offset) (offset + AnyRound.localLength r)

def Assumptions (_state : Vector (F p) t) := True

def Spec (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t))
    (state : Vector (F p) t) (out : Vector (F p) t) :=
  out = permuteVal mds rounds state

instance elaborated (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t)) :
    ElaboratedCircuit (F p) (fields t) (fields t) where
  main := main mds rounds
  localLength _ := localLength rounds
  output := output mds rounds
  localLength_eq state offset := by
    induction rounds generalizing state offset with
    | nil => rfl
    | cons r rs ih =>
      simp only [main, localLength, Circuit.bind_localLength_eq, ih]
      simp [circuit_norm, AnyRound.circuit]
  output_eq state offset := by
    induction rounds generalizing state offset with
    | nil => rfl
    | cons r rs ih =>
      simp only [main, output, Circuit.bind_output_eq, ih]
      simp [circuit_norm, AnyRound.circuit]
  subcircuitsConsistent state offset := by
    induction rounds generalizing state offset with
    | nil => simp [main, circuit_norm]
    | cons r rs ih =>
      show ((main mds (r :: rs) state).operations offset).SubcircuitsConsistent offset
      simp only [main, Circuit.bind_operations_eq]
      unfold Operations.SubcircuitsConsistent
      rw [Operations.forAll_append]
      constructor
      · simp [circuit_norm]
      · have h := ih ((subcircuit (AnyRound.circuit mds r) state).output offset)
          (offset + (subcircuit (AnyRound.circuit mds r) state).localLength offset)
        unfold Operations.SubcircuitsConsistent at h
        rw [add_comm]
        exact h

theorem soundness (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t)) :
    Soundness (F p) (elaborated mds rounds) Assumptions (Spec mds rounds) := by
  induction rounds with
  | nil =>
    intro offset env input_var input h_input _ _
    simp only [Spec, permuteVal]
    exact h_input
  | cons r rs ih =>
    intro offset env input_var input h_input _ h_holds
    change Circuit.ConstraintsHold.Soundness env ((main mds (r :: rs) input_var).operations offset) at h_holds
    simp only [main, Circuit.ConstraintsHold.bind_soundness] at h_holds
    obtain ⟨h_round, h_tail⟩ := h_holds
    simp only [circuit_norm, AnyRound.circuit, AnyRound.Assumptions, AnyRound.Spec] at h_round
    have h_ih := ih _ env _ _ rfl trivial h_tail
    simp only [Spec, permuteVal] at h_ih ⊢
    simp only [circuit_norm, AnyRound.circuit] at h_ih
    simp only [circuit_norm] at h_input
    simp only [circuit_norm, output]
    rw [h_ih, h_round, h_input]

theorem completeness (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t)) :
    Completeness (F p) (elaborated mds rounds) Assumptions := by
  induction rounds with
  | nil =>
    intro offset env input_var _ input _ _
    simp [circuit_norm, main]
  | cons r rs ih =>
    intro offset env input_var h_env input h_input _
    change env.UsesLocalWitnessesCompleteness offset ((main mds (r :: rs) input_var).operations offset) at h_env
    simp only [main, Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
    obtain ⟨h_env_round, h_env_tail⟩ := h_env
    show Circuit.ConstraintsHold.Completeness env ((main mds (r :: rs) input_var).operations offset)
    simp only [main, Circuit.ConstraintsHold.bind_completeness]
    constructor
    · simp only [circuit_norm, AnyRound.circuit, AnyRound.Assumptions] at h_env_round ⊢
    · exact ih _ env _ h_env_tail _ rfl trivial

def circuit (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t)) :
    FormalCircuit (F p) (fields t) (fields t) :=
  { elaborated mds rounds with
    Assumptions
    Spec := Spec mds rounds
    soundness := soundness mds rounds
    completeness := completeness mds rounds }

end Ragu.Circuits.Poseidon.Permutation
