import Ragu.Foundation.Pasta.Basic

namespace Ragu.Foundation.Pasta.Tests.Basic

open Ragu.Foundation.Pasta
open CompElliptic.Fields.Pasta

example : Ragu.Core.Primes.p = PALLAS_BASE_CARD := p_eq_pallasBaseCard
example : Ragu.Core.Primes.q = PALLAS_SCALAR_CARD := q_eq_pallasScalarCard
example : Nat.Prime PALLAS_BASE_CARD := pallas_base_prime
example : Nat.Prime PALLAS_SCALAR_CARD := pallas_scalar_prime
example : Nat.card PallasPoint = Ragu.Core.Primes.q := pallas_group_order
example : Nat.card VestaPoint = Ragu.Core.Primes.p := vesta_group_order

example {P : PallasPoint} (hP : 2 • P = 0) : P = 0 :=
  pallas_no_two_torsion hP

example {P : VestaPoint} (hP : 2 • P = 0) : P = 0 :=
  vesta_no_two_torsion hP

end Ragu.Foundation.Pasta.Tests.Basic
