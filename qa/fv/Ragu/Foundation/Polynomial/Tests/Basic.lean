import Ragu.Foundation.Polynomial

namespace Ragu.Foundation.Polynomial.Tests.Basic

open CompPoly
open Finset Fintype MvPolynomial
open Ragu.Foundation.Polynomial

example (x : ℚ) : ((CPolynomial.X + 1 : CPolynomial ℚ).eval x) = x + 1 := by
  simp

example {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {n : ℕ} {p : MvPolynomial (Fin n) F} (hp : p ≠ 0) :
    (#{f ∈ Fintype.piFinset fun _ => (Finset.univ : Finset F) |
        MvPolynomial.eval f p = 0} : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ n
      ≤ (p.totalDegree : ℚ≥0) / Fintype.card F :=
  schwartz_zippel_fin hp

end Ragu.Foundation.Polynomial.Tests.Basic
