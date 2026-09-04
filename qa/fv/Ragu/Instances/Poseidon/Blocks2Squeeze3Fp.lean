import Ragu.Circuits.Poseidon.Sponge
import Ragu.Circuits.Poseidon.ParamsFp
import Ragu.Core

/-!
`Sponge::new` → eight `absorb`s → three `squeeze`s over `PoseidonFp`.

This is the shape `Hash1Fp` / `Hash4Fp` cannot reach. Eight elements at
`RATE = 4` cross a block boundary, so Rust permutes the buffered block when
the fifth element arrives and again at `squeeze`: two permutations over the
same state. That is where a bug contaminating the capacity word across a
block boundary would show up, and it is what `Sponge.Blocks` models.

The three squeezes come out of the second permutation without triggering a
third — `get_rate` takes the rate words, reverses them, and `squeeze` pops the
last — so the `i`-th squeezed element is state word `i`. Serializing words
`0, 1, 2` is what pins that reading against Rust.
-/

namespace Ragu.Instances.Poseidon.Blocks2Squeeze3Fp

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- The Pasta `Fp` permutation, as in `Hash1Fp`: the generated MDS matrix and
round constants, scheduled as 4 full, 56 partial, 4 full rounds. -/
def params : Circuits.Poseidon.Sponge.Params (F p) 5 :=
  { mds := Circuits.Poseidon.ParamsFp.mds,
    rounds := Circuits.Poseidon.Sponge.schedule Circuits.Poseidon.ParamsFp.fullRounds
      Circuits.Poseidon.ParamsFp.partialRounds Circuits.Poseidon.ParamsFp.roundConstants }

/-- The eight absorbed wires, chunked into the two rate blocks Rust buffers
them into: `x₀ … x₃` are permuted in when `x₄` arrives, `x₄ … x₇` at
`squeeze`. -/
def deserializeInput (input : Vector (Expression (F p)) 8) :
    Var (ProvableVector (fields 4) 2) (F p) :=
  #v[#v[input[0], input[1], input[2], input[3]],
     #v[input[4], input[5], input[6], input[7]]]

/-- The three squeezed elements, in the order `squeeze` returns them. The
projection to state words `0, 1, 2` happens inside `Squeeze.circuit`. -/
def serializeOutput (output : Var (fields 3) (F p)) : Vector (Expression (F p)) 3 :=
  output

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation :=
    (Circuits.Poseidon.Sponge.Squeeze.circuit params 2 3 3
      (by decide) (by decide) (by decide) (by decide)).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Poseidon.Blocks2Squeeze3Fp
