import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Instances.Point.Hints

variable {p : ℕ} [Fact p.Prime]

/-- Read the `(x, y)` pair the honest prover has allocated at index `idx`
    of the `"alloc_mul_w"` witness table. `z` is computed as `x * y`.
    Instance-level glue: the table name is a caller-side convention, not
    part of the `AllocMul` circuit definition. -/
def readRow (hint : ProverHint (F p)) (idx : ℕ) : Ragu.Circuits.Core.AllocMul.Row (F p) :=
  let v := (hint "alloc_mul_w" 2).getD idx default
  ⟨v[0], v[1], v[0] * v[1]⟩

/-- Read one field element from the `"alloc_square_w"` witness table at
    `(idx, slot)`. Instance-level glue: the table name and layout are a
    caller-side convention. -/
def readSquareElem (hint : ProverHint (F p)) (idx slot : ℕ) : F p :=
  let v := (hint "alloc_square_w" 1).getD idx default
  v[slot]!

end Ragu.Instances.Point.Hints
