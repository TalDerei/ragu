import Ragu.Circuits.Poseidon.Sponge
import Ragu.Circuits.Poseidon.ParamsFp
import Ragu.Core

/-!
`Sponge::new` → `absorb(x₀)` … `absorb(x₃)` → `squeeze()` over `PoseidonFp`:
a full rate block, still one permutation, of the state `[x₀, x₁, x₂, x₃, 0]`,
returning its first word.
-/

namespace Ragu.Instances.Poseidon.Hash4Fp

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- The Pasta `Fp` permutation: the generated MDS matrix and round constants,
scheduled as 4 full, 56 partial, 4 full rounds (the round counts come from
the parameter module, so the schedule cannot drift from the constants). -/
def params : Circuits.Poseidon.Sponge.Params (F p) 5 :=
  { mds := Circuits.Poseidon.ParamsFp.mds,
    rounds := Circuits.Poseidon.Sponge.schedule Circuits.Poseidon.ParamsFp.fullRounds
      Circuits.Poseidon.ParamsFp.partialRounds Circuits.Poseidon.ParamsFp.roundConstants }

/-- Reads the extractor's flat input wires into the reimplementation's
structured input. -/
def deserializeInput (input : Vector (Expression (F p)) 4) : Var (fields 4) (F p) :=
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
    (Circuits.Poseidon.Sponge.Hash1.circuit params 4).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Poseidon.Hash4Fp
