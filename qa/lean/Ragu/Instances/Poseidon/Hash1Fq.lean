import Ragu.Circuits.Poseidon.Sponge
import Ragu.Circuits.Poseidon.ParamsFq
import Ragu.Core

/-!
`Sponge::new` → `absorb(x)` → `squeeze()` over `PoseidonFq`: one permutation
of the state `[x, 0, 0, 0, 0]`, returning its first word.
-/

namespace Ragu.Instances.Poseidon.Hash1Fq

@[reducible]
def p := Core.Primes.q

/-- The Pasta `Fq` permutation: the generated MDS matrix and round constants,
scheduled as 4 full, 56 partial, 4 full rounds. -/
def params : Circuits.Poseidon.Sponge.Params (F p) 5 :=
  { mds := Circuits.Poseidon.ParamsFq.mds,
    rounds := Circuits.Poseidon.Sponge.schedule 8 56 Circuits.Poseidon.ParamsFq.roundConstants }

def deserializeInput (input : Vector (Expression (F p)) 1) : Var (fields 1) (F p) :=
  input

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation :=
    (Circuits.Poseidon.Sponge.Hash1.circuit params 1).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Poseidon.Hash1Fq
