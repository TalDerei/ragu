import Clean.Circuit
import Ragu.Circuits.Element.Fold

namespace Ragu.Circuits.Horner.Ky
variable {p : ℕ} [Fact p.Prime]

/-- `Horner::finish_ky` (`ragu_circuits/src/horner.rs`): after streaming `n`
coefficients into a `Horner` buffer, write the constant `1` as one more
coefficient and finish. The trailing step is `acc.mul(point).add(one)`, so
the trace is `Element::fold` over the `n + 1` elements
`[c₀, …, c_{n-1}, 1]` with `point` as the scale factor — every multiplication
gate is a `Fold` gate, and the constant only changes the final (gate-free)
addition. The reimpl therefore *is* `Fold.circuit (n + 1)` applied to the
coefficient vector with `1` pushed on the end, exactly as Rust delegates to
the same `Horner::write` path for the constant term. -/
structure Input (n : ℕ) (F : Type) where
  coefficients : Vector F n
  point : F
deriving ProvableStruct

/-- Delegates to `Element.Fold` over the coefficients with `1` appended,
mirroring `finish_ky`'s trailing constant term. -/
def main (n : ℕ) (input : Var (Input n) (F p)) : Circuit (F p) (Expression (F p)) :=
  Element.Fold.circuit (n + 1) ⟨input.coefficients.push 1, input.point⟩

/-- No precondition: Horner evaluation is total. -/
def Assumptions {n : ℕ} (_input : Input n (F p)) := True

/-- Horner evaluation of `coeffs` at `y`, highest degree first:
`(…((c₀·y + c₁)·y + c₂)…)·y + c_m`. This is the value-level shape of
`Fold.Spec` for a nonempty vector. -/
def horner {m : ℕ} (coeffs : Vector (F p) (m + 1)) (y : F p) : F p :=
  Fin.foldl m (fun acc (i : Fin m) => acc * y + coeffs[i.val + 1]) coeffs[0]

/-- The output is the Horner evaluation of `[c₀, …, c_{n-1}, 1]` at `point`,
i.e. `Σᵢ cᵢ · pointⁿ⁻ⁱ + 1` — the $k(Y)$ convention of a trailing constant
`1` term. -/
def Spec {n : ℕ} (input : Input n (F p)) (output : F p) :=
  output = horner (input.coefficients.push 1) input.point

/-- Three wires per multiplication, one per coefficient after the first;
the trailing constant adds an addition, not a gate. -/
instance elaborated (n : ℕ) : ElaboratedCircuit (F p) (Input n) field where
  main := main n
  localLength _ := 3 * n
  localLength_eq input offset := by
    simp +arith [main, circuit_norm, Element.Fold.circuit]
  subcircuitsConsistent input offset := by
    simp [main, circuit_norm]

/-- `Element.Fold`'s spec, read at the coefficient vector with `1` pushed. -/
theorem soundness (n : ℕ) :
    Soundness (F p) (elaborated n) Assumptions Spec := by
  circuit_proof_start [Element.Fold.circuit, Element.Fold.Assumptions, Element.Fold.Spec]
  rw [h_holds]
  subst h_input
  simp only [horner, Vector.getElem_push, Vector.getElem_map, apply_dite (Expression.eval env),
    Expression.eval]

/-- `Element.Fold` is total. -/
theorem completeness (n : ℕ) :
    Completeness (F p) (elaborated n) Assumptions := by
  circuit_proof_start [Element.Fold.circuit, Element.Fold.Assumptions]

/-- `Horner::finish_ky`: evaluate at `point`, with a trailing constant `1`. -/
def circuit (n : ℕ) : FormalCircuit (F p) (Input n) field :=
  { elaborated n with
    Assumptions
    Spec
    soundness := soundness n
    completeness := completeness n }

end Ragu.Circuits.Horner.Ky
