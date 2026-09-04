import Ragu.Circuits.Poseidon.Sponge
import Ragu.Circuits.Poseidon.ParamsFp
import Ragu.Core

/-!
`Sponge::new` → six `absorb`s → two `squeeze`s over `PoseidonFp`: one full
rate block and a two-element tail.

Rust permutes when the fifth element arrives (the first block is full) and
again at `squeeze`, on a state carrying only `[x₄, x₅]` in its first two
words — the ragged shape `Blocks2Squeeze3Fp` cannot reach, since its blocks
are uniform. This is `Sponge.Ragged` at one full block and a tail of two.
-/

namespace Ragu.Instances.Poseidon.Blocks1Tail2Squeeze2Fp

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- The Pasta `Fp` permutation, as in `Hash1Fp`. -/
def params : Circuits.Poseidon.Sponge.Params (F p) 5 :=
  { mds := Circuits.Poseidon.ParamsFp.mds,
    rounds := Circuits.Poseidon.Sponge.schedule Circuits.Poseidon.ParamsFp.fullRounds
      Circuits.Poseidon.ParamsFp.partialRounds Circuits.Poseidon.ParamsFp.roundConstants }

/-- The six absorbed wires as one full block and the two-element tail, in
absorption order. -/
def deserializeInput (input : Vector (Expression (F p)) 6) :
    Var (Circuits.Poseidon.Sponge.Ragged.Input 1 3 1) (F p) :=
  (#v[#v[input[0], input[1], input[2], input[3]]], #v[input[4], input[5]])

/-- The two squeezed elements, in the order `squeeze` returns them. -/
def serializeOutput (output : Var (fields 2) (F p)) : Vector (Expression (F p)) 2 :=
  output

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation :=
    (Circuits.Poseidon.Sponge.Ragged.circuit params 1 3 1 2
      (by decide) (by decide) (by decide) (by decide)).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Poseidon.Blocks1Tail2Squeeze2Fp
