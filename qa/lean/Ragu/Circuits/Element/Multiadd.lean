import Clean.Circuit

namespace Ragu.Circuits.Element.Multiadd
variable {p : ℕ} [Fact p.Prime]

/-- `multiadd` is variadic (`&[Element]` + `&[F]`). This extraction
instance fixes length 3 as a representative choice; a length-polymorphic
reimpl would require dependent-type machinery that Clean doesn't
currently expose. Parameterized over the three coefficients — the
extraction pins specific values, but the reimpl's soundness/completeness
are universal over any coefficient choice. -/
structure Input (F : Type) where
  x0 : F
  x1 : F
  x2 : F
deriving ProvableStruct

def main (c0 c1 c2 : F p) (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  -- Mirrors the production linear combination via `dr.add`; no initial
  -- zero (unlike `sum`). Explicit `Expression.const` matches autogen form.
  return Expression.const c0 * input.x0
       + Expression.const c1 * input.x1
       + Expression.const c2 * input.x2

def Assumptions (_c0 _c1 _c2 : F p) (_input : Input (F p)) := True

def Spec (c0 c1 c2 : F p) (input : Input (F p)) (output : F p) :=
  output = c0 * input.x0 + c1 * input.x1 + c2 * input.x2

instance elaborated (c0 c1 c2 : F p) : ElaboratedCircuit (F p) Input field where
  main := main c0 c1 c2
  localLength _ := 0

theorem soundness (c0 c1 c2 : F p) :
    Soundness (F p) (elaborated c0 c1 c2) (Assumptions c0 c1 c2) (Spec c0 c1 c2) := by
  circuit_proof_start

theorem completeness (c0 c1 c2 : F p) :
    Completeness (F p) (elaborated c0 c1 c2) (Assumptions c0 c1 c2) := by
  circuit_proof_start

def circuit (c0 c1 c2 : F p) : FormalCircuit (F p) Input field :=
  { elaborated c0 c1 c2 with
    Assumptions := Assumptions c0 c1 c2,
    Spec := Spec c0 c1 c2,
    soundness := soundness c0 c1 c2,
    completeness := completeness c0 c1 c2 }

end Ragu.Circuits.Element.Multiadd
