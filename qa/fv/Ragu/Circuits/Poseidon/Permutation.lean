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

The schedule is walked by explicit recursion rather than by one of Clean's
loop combinators, which deserves a justification.

`Circuit.foldl` requires the body to be `ConstantOutput`. That holds for a
full round — its output words are the MDS image of the S-box result wires,
which sit at offsets fixed by the round's position — but not for a partial
round, which carries four of its five output words as expressions in its
input. No restructuring of the body fixes that: the linear layers emit no
operations, so there is no fresh wire for the body to end on, and allocating
one would change the trace. `Circuit.foldlRange` drops the `ConstantOutput`
requirement, but its lemmas leave `Circuit.FoldlM.foldlAcc` unexpanded, so
the soundness chaining is the same induction either way.

Splitting the schedule into three uniform segments — full, partial, full —
would let the two full runs use `Circuit.foldl` and pick up its length,
output and consistency lemmas from `circuit_norm`; the partial run would
still need `foldlRange` and its own induction. That refactor is worth doing
and has not been done here.
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

/-- Dispatches to the full or partial round circuit, so that the schedule
below can treat both kinds uniformly. -/
def main (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t)
    (state : Var (fields t) (F p)) : Circuit (F p) (Var (fields t) (F p)) :=
  match r with
  | .full rc => Round.Full.circuit ⟨mds, rc⟩ state
  | .part rc => Round.Partial.circuit ⟨mds, rc⟩ state

/-- Wires one round allocates: `9 * t` for a full round (three `Element.Mul`
gates per state word), `9` for a partial one (the first word only). -/
def localLength : RoundSpec (F p) t → ℕ
  | .full _ => 9 * t
  | .part _ => 9

/-- The state wires this round produces, in either round kind. -/
def output (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t)
    (state : Var (fields t) (F p)) (offset : ℕ) : Var (fields t) (F p) :=
  match r with
  | .full rc => (Round.Full.circuit ⟨mds, rc⟩).output state offset
  | .part rc => (Round.Partial.circuit ⟨mds, rc⟩).output state offset

/-- No precondition: both round kinds are total in their input. -/
def Assumptions (_state : Vector (F p) t) := True

/-- The output is this round's value-level function applied to the input. -/
def Spec (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t)
    (state : Vector (F p) t) (out : Vector (F p) t) :=
  out = roundVal mds r state

/-- Every field dispatches on the round kind; each case is the corresponding
`Round` sub-gadget, so nothing is proved twice. -/
instance elaborated (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t) :
    ElaboratedCircuit (F p) (fields t) (fields t) (main mds r) where
  localLength _ := localLength r
  output := output mds r
  localLength_eq state offset := by
    cases r <;> simp [main, localLength, circuit_norm, Round.Full.circuit, Round.Partial.circuit]
  output_eq state offset := by
    cases r <;> simp [main, output, circuit_norm]
  subcircuitsConsistent state offset := by
    cases r <;> simp [main, circuit_norm]
  channelsLawful := by
    cases r <;> simp [main, circuit_norm, Round.Full.circuit, Round.Partial.circuit]

/-- Immediate from the underlying round's `Spec` in either case. -/
theorem soundness (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t) :
    Soundness (F p) (Input := (fields t)) (Output := (fields t)) (main mds r) Assumptions (Spec mds r) := by
  cases r with
  | full rc =>
    circuit_proof_start [Round.Full.circuit, Round.Full.Assumptions, Round.Full.Spec]
    exact h_holds
  | part rc =>
    circuit_proof_start [Round.Partial.circuit, Round.Partial.Assumptions, Round.Partial.Spec]
    exact h_holds

/-- Immediate from the underlying round's completeness in either case. -/
theorem completeness (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t) :
    Completeness (F p) (Input := (fields t)) (Output := (fields t)) (main mds r) Assumptions := by
  cases r with
  | full rc =>
    circuit_proof_start [Round.Full.circuit, Round.Full.Assumptions]
  | part rc =>
    circuit_proof_start [Round.Partial.circuit, Round.Partial.Assumptions]

/-- One Poseidon round of either kind, as a single sub-gadget. -/
def circuit (mds : Vector (Vector (F p) t) t) (r : RoundSpec (F p) t) :
    FormalCircuit (F p) (fields t) (fields t) :=
  { main := main mds r,
    elaborated := elaborated mds r,
    requirementsChannelsLawful := by
      cases r <;> simp [main, circuit_norm, Round.Full.circuit, Round.Partial.circuit]
    Assumptions
    Spec := Spec mds r
    soundness := soundness mds r
    completeness := completeness mds r }

end AnyRound

/-- The rounds of the schedule, applied in order. Each is the boxed
`AnyRound` sub-gadget, so the recursion adds no constraints of its own. -/
def main (mds : Vector (Vector (F p) t) t) :
    List (RoundSpec (F p) t) → Var (fields t) (F p) → Circuit (F p) (Var (fields t) (F p))
  | [], state => pure state
  | r :: rs, state => do
    let state ← AnyRound.circuit mds r state
    main mds rs state

/-- Wires the schedule allocates: the sum over its rounds. -/
def localLength : List (RoundSpec (F p) t) → ℕ
  | [] => 0
  | r :: rs => AnyRound.localLength r + localLength rs

/-- The state wires after the whole schedule, threaded round by round. -/
def output (mds : Vector (Vector (F p) t) t) :
    List (RoundSpec (F p) t) → Var (fields t) (F p) → ℕ → Var (fields t) (F p)
  | [], state, _ => state
  | r :: rs, state, offset =>
    output mds rs (AnyRound.output mds r state offset) (offset + AnyRound.localLength r)

/-- No precondition: every round is total in its input. -/
def Assumptions (_state : Vector (F p) t) := True

/-- The output is the schedule applied to the input state. -/
def Spec (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t))
    (state : Vector (F p) t) (out : Vector (F p) t) :=
  out = permuteVal mds rounds state

/-- Length, output and subcircuit consistency all follow by induction on the
schedule, since each round contributes a fixed number of wires. -/
instance elaborated (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t)) :
    ElaboratedCircuit (F p) (fields t) (fields t) (main mds rounds) where
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
  channelsLawful := by
    induction rounds with
    | nil => simp [main, circuit_norm]
    | cons r rs ih =>
      simp [main, circuit_norm, AnyRound.circuit]
      intro input_var offset
      have h := ih (AnyRound.output mds r input_var offset) (offset + AnyRound.localLength r)
      obtain ⟨h_channels, h_guarantees, h_subcircuits⟩ := h
      refine ⟨by simpa using h_channels, ?_, ?_⟩
      · simpa [Operations.InChannelsOrGuarantees] using h_guarantees
      · rwa [Operations.subcircuitChannelsLawful_iff_forAllNoOffset] at h_subcircuits

/-- Each round's `Spec` gives one `roundVal` step; chaining them along the
schedule gives `permuteVal`. -/
theorem soundness (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t)) :
    Soundness (F p) (Input := (fields t)) (Output := (fields t)) (main mds rounds) Assumptions (Spec mds rounds) := by
  induction rounds with
  | nil =>
    intro offset env input_var input h_input _ _
    simp only [Spec, permuteVal]
    exact ⟨h_input, by simp [main, circuit_norm]⟩
  | cons r rs ih =>
    intro offset env input_var input h_input _ h_holds
    change ConstraintsHold.Soundness env ((main mds (r :: rs) input_var).operations offset) at h_holds
    simp only [main, ConstraintsHold.Soundness, Circuit.bind_forAllNoOffset] at h_holds
    obtain ⟨h_round, h_tail⟩ := h_holds
    simp only [circuit_norm, AnyRound.circuit, AnyRound.Assumptions, AnyRound.Spec] at h_round
    have h_ih := ih _ env _ _ rfl trivial h_tail
    obtain ⟨h_ih, h_tail_requirements⟩ := h_ih
    simp only [Spec, permuteVal] at h_ih ⊢
    simp only [circuit_norm, AnyRound.circuit] at h_ih
    simp only [circuit_norm] at h_input
    simp only [circuit_norm, output]
    constructor
    · rw [h_ih, h_round, h_input]
    · simp only [main, Circuit.bind_forAllNoOffset]
      constructor
      · simp [circuit_norm, AnyRound.circuit]
      · simpa [circuit_norm, AnyRound.circuit] using h_tail_requirements

/-- Every round is total, so the honest witness exists at each step. -/
theorem completeness (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t)) :
    Completeness (F p) (Input := (fields t)) (Output := (fields t)) (main mds rounds) Assumptions := by
  induction rounds with
  | nil =>
    intro offset env input_var _ input _ _
    simp [circuit_norm, main]
  | cons r rs ih =>
    intro offset env input_var h_env input h_input _
    change env.UsesLocalWitnessesCompleteness offset ((main mds (r :: rs) input_var).operations offset) at h_env
    simp only [main, Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
    obtain ⟨h_env_round, h_env_tail⟩ := h_env
    show ConstraintsHold.Completeness env ((main mds (r :: rs) input_var).operations offset)
    simp only [main, ConstraintsHold.Completeness, Circuit.bind_forAllNoOffset]
    constructor
    · simp only [circuit_norm, AnyRound.circuit, AnyRound.Assumptions] at h_env_round ⊢
    · exact ih _ env _ h_env_tail _ rfl trivial

/-- A Poseidon permutation: the rounds of `rounds`, applied in order. -/
def circuit (mds : Vector (Vector (F p) t) t) (rounds : List (RoundSpec (F p) t)) :
    FormalCircuit (F p) (fields t) (fields t) :=
  { main := main mds rounds,
    elaborated := elaborated mds rounds,
    requirementsChannelsLawful := by
      induction rounds with
      | nil => simp [main, circuit_norm]
      | cons r rs ih =>
        simp [main, circuit_norm, AnyRound.circuit]
        intro input offset
        have h := ih (AnyRound.output mds r input offset) (offset + AnyRound.localLength r)
        obtain ⟨h_channels, h_covered, h_requirements⟩ := h
        refine ⟨by simpa using h_channels, ?_, ?_⟩
        · intro channel h_mem
          have h := h_covered channel h_mem
          have h_empty : ElaboratedCircuit.channelsWithGuarantees (main mds rs) = [] := rfl
          rw [h_empty] at h
          rcases h with h | h <;> simp at h
        · simpa [ConstraintsHold.Shallow, Operations.InChannelsOrRequirements] using h_requirements
    Assumptions
    Spec := Spec mds rounds
    soundness := soundness mds rounds
    completeness := completeness mds rounds }

end Ragu.Circuits.Poseidon.Permutation
