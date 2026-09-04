import Ragu.Circuits.Poseidon.Sponge
import Ragu.Circuits.Poseidon.ParamsFq
import Ragu.Core

/-!
`Sponge::new` → `absorb(x)` → `squeeze()` over `PoseidonFq`: one permutation
of the state `[x, 0, 0, 0, 0]`, returning its first word.
-/

namespace Ragu.Instances.Poseidon.Hash1Fq

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.q

/-- The Pasta `Fq` permutation: the generated MDS matrix and round constants,
scheduled as 4 full, 56 partial, 4 full rounds (the round counts come from
the parameter module, so the schedule cannot drift from the constants). -/
def params : Circuits.Poseidon.Sponge.Params (F p) 5 :=
  { mds := Circuits.Poseidon.ParamsFq.mds,
    rounds := Circuits.Poseidon.Sponge.schedule Circuits.Poseidon.ParamsFq.fullRounds
      Circuits.Poseidon.ParamsFq.partialRounds Circuits.Poseidon.ParamsFq.roundConstants }

/-- Reads the extractor's flat input wires into the reimplementation's
structured input. -/
def deserializeInput (input : Vector (Expression (F p)) 1) : Var (fields 1) (F p) :=
  input

/-- Writes the reimplementation's output back to the extractor's flat
output wires. -/
def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation :=
    (Circuits.Poseidon.Sponge.Hash1.circuit params 1 (by decide)
      (by decide)).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Poseidon.Hash1Fq
