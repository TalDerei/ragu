import Clean.Circuit

namespace Ragu.Core.Primes

def p := 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
def q := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

axiom p_prime : Fact p.Prime
axiom q_prime : Fact q.Prime

instance : Fact p.Prime := p_prime
instance : Fact q.Prime := q_prime

@[reducible]
def Fp := F p

@[reducible]
def Fq := F q

instance : Field (F p) := inferInstance
instance : Field (F q) := inferInstance

-- 2 is not zero in both fields
instance : NeZero (2 : F p) where
  out := by native_decide

instance : NeZero (2 : F q) where
  out := by native_decide

end Ragu.Core.Primes


namespace Ragu.Core.Statements

/-- A concrete circuit instance subject to formal verification.

Bundles the concrete prime field, the structured `Clean` `reimplementation`
that the soundness/completeness proofs are about, and the serialization glue
that maps between the extractor's flat input/output vectors and the
reimplementation's structured types.

The reimplementation is tied to the Rust circuit by the fingerprint
equivalence check: `Ragu.Fingerprint` computes a canonical digest of the
operations and outputs the reimplementation emits, and CI compares it against
the digest the Rust extractor computes from the extracted trace. -/
structure FormalInstance where
  p : ℕ
  [pPrime : Fact p.Prime]

  {Input : TypeMap}
  [InputCircuit : CircuitType Input]
  [InputValueProvable : ProvableType (Value Input)]

  {Output : TypeMap}
  [OutputProvable : ProvableType Output]

  deserializeInput : Vector (Expression (F p)) (size (Value Input)) → Var Input (F p)
  serializeOutput : Var Output (F p) → Vector (Expression (F p)) (size Output)

  reimplementation : GeneralFormalCircuit.WithHint (F p) Input Output

end Statements

-- this seems generally useful: whenever we allow `eval` to be rewritten to a concrete `CircuitType` instance,
-- we can immediately unfold it with `circuit_norm`!
attribute [circuit_norm] CircuitType.evalVerifier CircuitType.evalProver

instance {Hint : TypeMap} {F : Type} [Inhabited (Hint F)] :
    Inhabited (Var (UnconstrainedDep Hint) F) where
  default := fun _ => default

-- missing arithmetic instances

instance {F : Type} [Field F] : HMul (Value field F) F F where
  hMul (x : F) y := x * y

instance {F : Type} [Field F] : HMul (Value field F) (field F) F where
  hMul (x : F) (y : F) := x * y

instance {F : Type} [Field F] : HMul (ProverValue field F) F F where
  hMul (x : F) (y : F) := x * y

instance {F : Type} [Field F] : HDiv (Value field F) (Value field F) F where
  hDiv (x : F) (y : F) := x / y

instance {F : Type} [Field F] : OfNat (Value field F) 0 where
  ofNat := (0 : F)

instance {F : Type} [Field F] : OfNat (Value field F) 1 where
  ofNat := (1 : F)

instance {F : Type} [Field F] : OfNat (ProverValue field F) 0 where
  ofNat := (0 : F)

instance {F : Type} [Field F] : OfNat (ProverValue field F) 1 where
  ofNat := (1 : F)

end Ragu.Core
