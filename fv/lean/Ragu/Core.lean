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
