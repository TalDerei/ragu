import Ragu.Circuits.Poseidon.Sponge
import Ragu.Circuits.Poseidon.ParamsFp
import Ragu.Core

/-!
`Sponge::new` → `absorb(x)` → `squeeze()` → `absorb(y)` → `squeeze()` over
`PoseidonFp`: absorption *after* a squeeze.

The first `squeeze` permutes `[x, 0, 0, 0, 0]`. The second `absorb` finds the
sponge in squeeze mode and re-enters absorb mode on that permuted state,
buffering `y`; the second `squeeze` adds `y` into word `0` of the permuted
state and permutes again. Two permutations over two width-1 batches —
`Squeeze.circuit` at `n = 2, w = 0`, the family's narrow-block reading.

Only the final squeeze is collected. The first squeeze's output is word `0`
of the intermediate state, which `Hash1Fp` already pins.
-/

namespace Ragu.Instances.Poseidon.InterleavedFp

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- The Pasta `Fp` permutation, as in `Hash1Fp`. -/
def params : Circuits.Poseidon.Sponge.Params (F p) 5 :=
  { mds := Circuits.Poseidon.ParamsFp.mds,
    rounds := Circuits.Poseidon.Sponge.schedule Circuits.Poseidon.ParamsFp.fullRounds
      Circuits.Poseidon.ParamsFp.partialRounds Circuits.Poseidon.ParamsFp.roundConstants }

/-- The two absorbed wires as two width-1 batches, in absorption order. -/
def deserializeInput (input : Vector (Expression (F p)) 2) :
    Var (ProvableVector (fields 1) 2) (F p) :=
  #v[#v[input[0]], #v[input[1]]]

/-- The final squeezed element. -/
def serializeOutput (output : Var (fields 1) (F p)) : Vector (Expression (F p)) 1 :=
  output

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation :=
    (Circuits.Poseidon.Sponge.Squeeze.circuit params 2 0 1
      (by decide) (by decide) (by decide) (by decide)).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Poseidon.InterleavedFp
