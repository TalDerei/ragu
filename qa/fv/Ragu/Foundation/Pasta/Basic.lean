import Ragu.Core
import CompElliptic.Curves.PastaOrder

/-!
# Pasta cycle certificates

Thin, provenance-pinned names for the Pasta field and curve facts that later Ragu protocol
formalization needs. The underlying certificates come from the direct CompElliptic dependency at
commit 2c0444035a84db957f27f06433715058d1e890ad:

* CompElliptic/Fields/Pasta.lean for both field primes;
* CompElliptic/Curves/Pasta.lean for the no-2-torsion ingredients; and
* CompElliptic/Curves/PastaOrder.lean for both curve orders.

These aliases cover both directions of the Pasta cycle. They do not identify either curve with
Ragu's unfinished recursive verifier or supply a transcript, commitment scheme, or acceptance
theorem.
-/

namespace Ragu.Foundation.Pasta

open CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.CurveOrder
open CompElliptic.Fields.Pasta
open CompElliptic.Curves.Pasta

/-- The Pallas base field, definitionally Ragu's Fp. -/
abbrev PallasBase := PallasBaseField

/-- The Pallas scalar field, definitionally Ragu's Fq and Vesta's base field. -/
abbrev PallasScalar := PallasScalarField

/-- The Vesta base field. -/
abbrev VestaBase := VestaBaseField

/-- The Vesta scalar field. -/
abbrev VestaScalar := VestaScalarField

/-- The complete Pallas short-Weierstrass point group. -/
abbrev PallasPoint := SWPoint Pallas.curve

/-- The complete Vesta short-Weierstrass point group. -/
abbrev VestaPoint := SWPoint Vesta.curve

/-- Ragu's first modulus is the Pallas base-field cardinality. -/
theorem p_eq_pallasBaseCard :
    Ragu.Core.Primes.p = PALLAS_BASE_CARD := rfl

/-- Ragu's second modulus is the Pallas scalar/Vesta base-field cardinality. -/
theorem q_eq_pallasScalarCard :
    Ragu.Core.Primes.q = PALLAS_SCALAR_CARD := rfl

/-- Certified primality of the Pallas base-field cardinality. -/
theorem pallas_base_prime : Nat.Prime PALLAS_BASE_CARD :=
  PALLAS_BASE_is_prime

/-- Certified primality of the Pallas scalar/Vesta base-field cardinality. -/
theorem pallas_scalar_prime : Nat.Prime PALLAS_SCALAR_CARD :=
  PALLAS_SCALAR_is_prime

/-- The Pallas group has order q, the opposite field's cardinality. -/
theorem pallas_group_order :
    Nat.card PallasPoint = Ragu.Core.Primes.q := by
  simpa [q_eq_pallasScalarCard] using Pallas.card_eq

/-- The Vesta group has order p, the opposite field's cardinality. -/
theorem vesta_group_order :
    Nat.card VestaPoint = Ragu.Core.Primes.p := by
  simpa [p_eq_pallasBaseCard] using Vesta.card_eq

/-- Pallas has no nonidentity point killed by 2. -/
theorem pallas_no_two_torsion {P : PallasPoint} (hP : 2 • P = 0) : P = 0 :=
  eq_zero_of_two_nsmul_eq_zero (by decide) Pallas.no_onCurve_y_zero hP

/-- Vesta has no nonidentity point killed by 2. -/
theorem vesta_no_two_torsion {P : VestaPoint} (hP : 2 • P = 0) : P = 0 :=
  eq_zero_of_two_nsmul_eq_zero (by decide) Vesta.no_onCurve_y_zero hP

end Ragu.Foundation.Pasta
