import Ragu.Core
import Ragu.Fingerprint.Sha256

/-!
# Canonical circuit fingerprints

A fingerprint is the SHA-256 digest of a canonical byte encoding of a
circuit's operation trace and output expressions. This module computes the
digest of a `FormalInstance`'s **reimplementation** — the structured `Clean`
circuit — instantiated at a canonical input vector.

The Rust extractor computes the same digest directly from its in-memory
extracted trace (`cargo run -p lean_extraction -- fingerprint`), and CI
compares the two outputs. A match shows that the reimplementation emits
exactly the operations and outputs of the Rust circuit, so the
soundness/completeness theorems proved about the reimplementation apply to
the circuit the proof system actually verifies. This is the "verification
key comparison" style of equivalence check.

## Encoding

All integers are unsigned 64-bit little-endian; field elements and the
modulus are 32-byte little-endian. The digest preimage is:

```text
"ragu-fv-fingerprint-v1"      (22 raw ASCII bytes, domain separator)
modulus                       (32 bytes)
inputLen                      (u64)
outputLen                     (u64)
opCount                       (u64)
op*                           (opCount operations)
output*                       (outputLen expressions)
```

Operations (`FlatOperation`, after flattening subcircuits):

```text
witness: 0x01 ++ count (u64)
assert:  0x02 ++ expr
```

Expressions:

```text
var:   0x01 ++ index (u64)
const: 0x02 ++ value (32 bytes)
add:   0x03 ++ expr ++ expr
mul:   0x04 ++ expr ++ expr
```

Witness computation functions are not encoded: the digest captures
allocations, constraints, and outputs, not witness generation. Lookup
operations are not supported and produce an error.

`Expression` has no constructor for input variables, so the circuit is
instantiated at the canonical input vector `#v[var ⟨2³² + 0⟩, ...]`; the
Rust encoder maps its `InputVar i` to a `var` with index `2³² + i`, and both
sides reject other variable indices in or beyond the input region, so the
two regions cannot collide.
-/

namespace Ragu.Fingerprint

/-- Wire index at which canonical input variables start (`2³²`). -/
def inputVarOffset : ℕ := 2 ^ 32

/-- Append `n` to `buf` as `bytes` little-endian bytes. -/
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
  | .witness m _ => pure (pushNat64 (buf.push 0x01) m)
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
