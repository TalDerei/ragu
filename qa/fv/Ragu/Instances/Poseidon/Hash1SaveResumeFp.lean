import Ragu.Instances.Poseidon.Hash1Fp

/-!
`Sponge::new` → `absorb(x)` → `save_state` → `resume` → `squeeze()` over
`PoseidonFp`.

This is the `Transcript` API's path through the sponge, and it is
*trace-identical* to `Hash1Fp`: `save_state` runs the permutation the first
`squeeze` would have run, and `resume` re-enters squeeze mode on exactly the
state that permutation produced. So the reimplementation and theorems are
`Hash1Fp`'s, unchanged. What this instance adds is the check that the Rust
save/resume path emits the same trace as the direct one — no missing
permutation, no extra constraint — which is the equivalence
`test_save_resume_produces_same_output_as_normal_sponge` tests on values
and this pins on the circuit.
-/

namespace Ragu.Instances.Poseidon.Hash1SaveResumeFp

/-- `Hash1Fp`'s instance: same circuit, reached through `save_state` /
`resume` on the Rust side. -/
def formal_instance : Core.Statements.FormalInstance :=
  Hash1Fp.formal_instance

end Ragu.Instances.Poseidon.Hash1SaveResumeFp
