import Ragu.Core
import Ragu.Fingerprint.Sha256

/-!
# Canonical circuit fingerprints

Computes the SHA-256 digest of a canonical byte encoding of the operation
trace and output expressions a `FormalInstance`'s reimplementation emits,
instantiated at the canonical input vector `#v[var ⟨2³² + 0⟩, ...]`. The
Rust extractor computes the same digest from its in-memory extracted trace,
and CI compares the two: a match means the reimplementation emits exactly
the operations and outputs of the Rust circuit.

The byte-level encoding, the input-variable index convention, and the trust
assumptions of the check are specified in the FV book
(`qa/lean/docs/src/ragu/fingerprint.md`); this module and
`qa/crates/lean_extraction/src/fingerprint.rs` implement that spec and must
stay in lockstep.
-/

namespace Ragu.Fingerprint

/-- Wire index at which canonical input variables start (`2³²`). -/
def inputVarOffset : ℕ := 2 ^ 32

/-- Append `n` to `buf` as `bytes` little-endian bytes.

Truncates if `n ≥ 2^(8 * bytes)`; callers must bound-check first, or the
encoding loses injectivity. -/
def pushNatLE (bytes : ℕ) (buf : ByteArray) (n : ℕ) : ByteArray :=
  (List.range bytes).foldl (fun acc i => acc.push (UInt8.ofNat ((n >>> (8 * i)) &&& 0xff))) buf

/-- Append a variable index or operation count as 8 little-endian bytes. -/
def pushNat64 : ByteArray → ℕ → ByteArray := pushNatLE 8

/-- Append a field element value or modulus as 32 little-endian bytes. -/
def pushNat256 : ByteArray → ℕ → ByteArray := pushNatLE 32

variable {p : ℕ}

/-- Append the canonical encoding of an expression.

Fails on variable indices at or above `bound` (the end of the canonical
input region), which could otherwise collide with encoded input variables. -/
def pushExpr (bound : ℕ) (buf : ByteArray) : Expression (F p) → Except String ByteArray
  | .var v =>
    if v.index < bound then
      pure (pushNat64 (buf.push 0x01) v.index)
    else
      throw s!"variable index {v.index} collides with the input variable region"
  | .const c => pure (pushNat256 (buf.push 0x02) c.val)
  | .add l r => do pushExpr bound (← pushExpr bound (buf.push 0x03) l) r
  | .mul l r => do pushExpr bound (← pushExpr bound (buf.push 0x04) l) r

/-- Append the canonical encoding of a flat operation. Witness computation
functions are not encoded; lookups are unsupported. -/
def pushFlatOp (bound : ℕ) (buf : ByteArray) : FlatOperation (F p) → Except String ByteArray
  | .witness m _ =>
    if m < 2 ^ 64 then
      pure (pushNat64 (buf.push 0x01) m)
    else
      throw s!"witness count {m} does not fit in 64 bits"
  | .assert e => pushExpr bound (buf.push 0x02) e
  | .lookup _ => throw "lookup operations are not supported by the fingerprint encoding"

end Ragu.Fingerprint

open Ragu.Fingerprint in
/-- The canonical fingerprint of this instance's `reimplementation`,
instantiated at the canonical input vector, as a lowercase hex digest.

CI compares this against the digest the Rust extractor computes from its
extracted trace; see the module documentation of `Ragu.Fingerprint`. -/
def Ragu.Core.Statements.FormalInstance.fingerprint
    (inst : Ragu.Core.Statements.FormalInstance) : Except String String :=
  letI := inst.pPrime
  letI := inst.InputCircuit
  letI := inst.InputValueProvable
  letI := inst.OutputProvable
  let inputLen := size (Value inst.Input)
  let outputLen := size inst.Output
  let bound := inputVarOffset + inputLen
  let input : Vector (Expression (F inst.p)) inputLen :=
    .ofFn fun i => var ⟨inputVarOffset + i.val⟩
  let circuit := inst.reimplementation (inst.deserializeInput input)
  let ops := (circuit.operations 0).toFlat
  let outputs := inst.serializeOutput (circuit.output 0)
  do
    -- `pushNatLE` truncates out-of-range values, so reject them up front.
    if inst.p ≥ 2 ^ 256 then
      throw s!"modulus does not fit in 256 bits"
    if inputLen ≥ inputVarOffset then
      throw s!"input length {inputLen} overflows the input variable region"
    let mut buf := "ragu-fv-fingerprint-v1".toUTF8
    buf := pushNat256 buf inst.p
    buf := pushNat64 buf inputLen
    buf := pushNat64 buf outputLen
    buf := pushNat64 buf ops.length
    for op in ops do
      buf ← pushFlatOp bound buf op
    for output in outputs.toList do
      buf ← pushExpr bound buf output
    return Sha256.hexDigest (Sha256.hash buf)
