/-!
# SHA-256

Minimal SHA-256 (FIPS 180-4) over `ByteArray`, used for circuit
fingerprints. Mirrors `qa/crates/lean_extraction/src/sha256.rs` and is
validated against the FIPS 180-2 test vectors on both sides.
-/

namespace Ragu.Fingerprint.Sha256

/-- The 64 SHA-256 round constants. -/
def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Initial hash state. -/
def h0 : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Right-rotation of a 32-bit word. Assumes `0 < n < 32`. -/
def rotr (x n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Pad a message: append `0x80`, then zeros until the length is 56 mod 64,
then the message length in bits as a 64-bit big-endian integer. -/
def pad (msg : ByteArray) : ByteArray :=
  let zeros := (120 - ((msg.size + 1) % 64)) % 64
  let bitLen := 8 * msg.size
  let lenBytes : Array UInt8 := .ofFn fun (i : Fin 8) =>
    UInt8.ofNat ((bitLen >>> (8 * (7 - i.val))) &&& 0xff)
  msg.push 0x80 ++ ⟨.replicate zeros 0⟩ ++ ⟨lenBytes⟩

/-- Compress the 64-byte block of `msg` starting at `off` into `state`. -/
def compress (state : Array UInt32) (msg : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  -- message schedule
  let mut w : Array UInt32 := .replicate 64 0
  for i in [0:16] do
    let word := (msg.get! (off + 4 * i)).toUInt32 <<< 24 |||
                (msg.get! (off + 4 * i + 1)).toUInt32 <<< 16 |||
                (msg.get! (off + 4 * i + 2)).toUInt32 <<< 8 |||
                (msg.get! (off + 4 * i + 3)).toUInt32
    w := w.set! i word
  for i in [16:64] do
    let s0 := rotr w[i - 15]! 7 ^^^ rotr w[i - 15]! 18 ^^^ (w[i - 15]! >>> 3)
    let s1 := rotr w[i - 2]! 17 ^^^ rotr w[i - 2]! 19 ^^^ (w[i - 2]! >>> 10)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  -- compression rounds
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := h + s1 + ch + k[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
           state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

/-- The SHA-256 digest (32 bytes) of `msg`. -/
def hash (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad msg
  let mut state := h0
  for block in [0 : padded.size / 64] do
    state := compress state padded (64 * block)
  let mut out := ByteArray.empty
  for word in state do
    out := out.push (word >>> 24).toUInt8
    out := out.push (word >>> 16).toUInt8
    out := out.push (word >>> 8).toUInt8
    out := out.push word.toUInt8
  return out

/-- Lowercase hex rendering of a byte array. -/
def hexDigest (bytes : ByteArray) : String :=
  bytes.foldl (init := "") fun acc b =>
    (acc.push (Nat.digitChar (b >>> 4).toNat)).push (Nat.digitChar (b &&& 0xf).toNat)

-- FIPS 180-2 test vectors, plus padding boundary cases (55- and 64-byte inputs).
example : hexDigest (hash "".toUTF8)
    = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by native_decide
example : hexDigest (hash "abc".toUTF8)
    = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by native_decide
example : hexDigest (hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8)
    = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by native_decide
example : hexDigest (hash ⟨.replicate 55 0x61⟩)
    = "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318" := by native_decide
example : hexDigest (hash ⟨.replicate 64 0x61⟩)
    = "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb" := by native_decide

end Ragu.Fingerprint.Sha256
