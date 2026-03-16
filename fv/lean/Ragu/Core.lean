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

instance : NeZero (2 : F p) where
  out := by native_decide

end Ragu.Core.Primes


namespace Ragu.Core.Statements

/-- Erase witness computation functions from flat operations,
    replacing them with `default`. This allows comparing circuit
    structure (constraints) while ignoring witness generation,
    which is not faithfully reproduced in the circuit export. -/
def FlatOperation.eraseCompute {F : Type} [Field F] : FlatOperation F → FlatOperation F
  | .witness m _ => .witness m (fun _ => default)
  | op => op

structure FormalInstance where
  p : ℕ
  pPrime : Fact p.Prime := by infer_instance

  inputLen : ℕ
  outputLen : ℕ

  exportedOperations : Var (ProvableVector field inputLen) (F p) → Operations (F p)
  exportedOutput : Var (ProvableVector field inputLen) (F p) → Vector (Expression (F p)) outputLen

  Input : TypeMap
  InputProvable : ProvableType Input := by infer_instance

  Output : TypeMap
  OutputProvable : ProvableType Output := by infer_instance

  deserializeInput : Var (ProvableVector field inputLen) (F p) → Var Input (F p)
  serializeOutput : Var Output (F p) → Var (ProvableVector field outputLen) (F p)

  Spec : Input (F p) → Output (F p) → Prop

  reimplementation : GeneralFormalCircuit (F p) Input Output

  -- Compare circuit constraints, ignoring witness generation
  same_constraints : ∀ (input : Var (ProvableVector field inputLen) (F p)),
    (input |> deserializeInput |> reimplementation |>.operations 0).toFlat.map FlatOperation.eraseCompute
    = (exportedOperations input).toFlat.map FlatOperation.eraseCompute

  same_output : ∀ (input : Var (ProvableVector field inputLen) (F p)),
    (input |> deserializeInput |> reimplementation |>.output 0 |> serializeOutput) = exportedOutput input

  -- NOTE: this can be relaxed by proving that the reimplementation spec implies the instance spec instead
  same_spec : ∀ input : Input (F p), ∀ output : Output (F p),
    (Spec input output) ↔ (reimplementation.Spec input output (fun _ _ => #[]))

end Ragu.Core.Statements
