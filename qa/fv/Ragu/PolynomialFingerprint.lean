import Ragu.Fingerprint

/-!
# Direct randomized polynomial fingerprints

This is the Lean half of `ragu-fv-polynomial-v1`. It evaluates a
`FormalInstance.reimplementation` directly at challenges derived from an
explicit seed. It does not construct a complete monomial representation of the
circuit; only each small gate assertion is normalized to validate its shape.

Every three-variable witness immediately followed by an assertion is decoded
as one production gate: the three Lean variables are the gate's `A`, `B`, and
`C` slots, the assertion is the `A * B - C` gate relation, and an independent
`D` slot plus the `C * D` relation are reconstructed here. All remaining
assertions are ordered linear constraints. Unsupported witness shapes,
lookups, and interactions fail closed.
-/

namespace Ragu.PolynomialFingerprint

open Ragu.Fingerprint

def formatTag : String := "ragu-fv-polynomial-v1"

def defaultPoints : ℕ := 2

/-- Maximum admitted total degree after geometric-sequence substitution. -/
def maxDegreeBound : ℕ := 2048

/-- Conservative total-degree bound for the four accumulated polynomials. -/
def degreeBound (inputs outputs gates constraints extras : ℕ) : ℕ :=
  max (3 * gates)
    (max (max inputs gates + constraints)
      (max (gates + extras) (max inputs gates + outputs)))

def pushBytes (buf bytes : ByteArray) : ByteArray := buf ++ bytes

def pushLengthPrefixed (buf bytes : ByteArray) : ByteArray :=
  pushBytes (pushNat64 buf bytes.size) bytes

/-- Read a byte array as one little-endian natural number. -/
def natLE (bytes : ByteArray) : ℕ :=
  (List.range bytes.size).foldl
    (fun acc i => acc + (bytes.get! i).toNat * 256 ^ i) 0

def hexNibble (byte : UInt8) : Option ℕ :=
  let n := byte.toNat
  if 0x30 ≤ n ∧ n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n ∧ n ≤ 0x66 then some (n - 0x61 + 10)
  else if 0x41 ≤ n ∧ n ≤ 0x46 then some (n - 0x41 + 10)
  else none

/-- Strictly parse exactly 32 bytes of hexadecimal seed material. -/
def parseSeed (hex : String) : Except String ByteArray := do
  let ascii := hex.toUTF8
  if ascii.size ≠ 64 then
    throw s!"seed must contain exactly 64 hexadecimal digits, got {ascii.size}"
  let mut seed := ByteArray.empty
  for i in [0:32] do
    let some hi := hexNibble (ascii.get! (2 * i))
      | throw s!"seed contains a non-hexadecimal digit at byte {i}"
    let some lo := hexNibble (ascii.get! (2 * i + 1))
      | throw s!"seed contains a non-hexadecimal digit at byte {i}"
    seed := seed.push (UInt8.ofNat (16 * hi + lo))
  return seed

structure ChallengeContext (p : ℕ) where
  seed : ByteArray
  instanceName : String
  point : ℕ

/-- Derive a 512-bit little-endian integer with two SHA-256 blocks and reduce
it modulo `p`. This mirrors `ChallengeContext::base` in Rust. -/
def challengeBase {p : ℕ} [Fact p.Prime] (ctx : ChallengeContext p)
    (label : String) : F p :=
  let challengeBytes := Id.run do
    let mut buf := formatTag.toUTF8
    buf := pushBytes buf ctx.seed
    buf := pushBytes buf (pushNat256 ByteArray.empty p)
    buf := pushLengthPrefixed buf ctx.instanceName.toUTF8
    buf := pushNat64 buf ctx.point
    buf := pushLengthPrefixed buf label.toUTF8
    return buf
  let firstBlock := Ragu.Fingerprint.Sha256.hash (challengeBytes.push 0)
  let secondBlock := Ragu.Fingerprint.Sha256.hash (challengeBytes.push 1)
  (natLE (firstBlock ++ secondBlock) : F p)

structure ChallengeBases (p : ℕ) where
  input : F p
  wireA : F p
  wireB : F p
  wireC : F p
  wireD : F p
  gateAbWeight : F p
  gateCdWeight : F p
  constraintWeight : F p
  extraWeight : F p
  outputWeight : F p

def ChallengeBases.new {p : ℕ} [Fact p.Prime] (ctx : ChallengeContext p) : ChallengeBases p := {
  input := challengeBase ctx "input"
  wireA := challengeBase ctx "wire-a"
  wireB := challengeBase ctx "wire-b"
  wireC := challengeBase ctx "wire-c"
  wireD := challengeBase ctx "wire-d"
  gateAbWeight := challengeBase ctx "gate-ab-weight"
  gateCdWeight := challengeBase ctx "gate-cd-weight"
  constraintWeight := challengeBase ctx "constraint-weight"
  extraWeight := challengeBase ctx "extra-weight"
  outputWeight := challengeBase ctx "output-weight" }

def powers {p : ℕ} [Fact p.Prime] (base : F p) (count : ℕ) : Array (F p) := Id.run do
  let mut out := #[]
  let mut current := base
  for _ in [0:count] do
    out := out.push current
    current := current * base
  return out

structure ChallengeValues (p : ℕ) where
  inputs : Array (F p)
  wireA : Array (F p)
  wireB : Array (F p)
  wireC : Array (F p)
  wireD : Array (F p)
  gateAbWeights : Array (F p)
  gateCdWeights : Array (F p)
  constraintWeights : Array (F p)
  outputWeights : Array (F p)

def ChallengeValues.new {p : ℕ} [Fact p.Prime] (bases : ChallengeBases p)
    (inputCount gateCount constraintCount outputCount : ℕ) : ChallengeValues p := {
  inputs := powers bases.input inputCount
  wireA := powers bases.wireA gateCount
  wireB := powers bases.wireB gateCount
  wireC := powers bases.wireC gateCount
  wireD := powers bases.wireD gateCount
  gateAbWeights := powers bases.gateAbWeight gateCount
  gateCdWeights := powers bases.gateCdWeight gateCount
  constraintWeights := powers bases.constraintWeight constraintCount
  outputWeights := powers bases.outputWeight outputCount }

def wireValue {p : ℕ} [Fact p.Prime] (values : ChallengeValues p)
    (inputCount gateCount index : ℕ) : Except String (F p) := do
  if inputVarOffset ≤ index then
    let input := index - inputVarOffset
    if input < inputCount then
      return values.inputs[input]!
    throw s!"input variable {input} is outside input arity {inputCount}"
  if index ≥ 3 * gateCount then
    throw s!"local variable {index} is outside {gateCount} three-wire gate encodings"
  let gate := index / 3
  match index % 3 with
  | 0 => return values.wireA[gate]!
  | 1 => return values.wireB[gate]!
  | _ => return values.wireC[gate]!

def evalExpression {p : ℕ} [Fact p.Prime] (values : ChallengeValues p)
    (inputCount gateCount : ℕ) : Expression (F p) → Except String (F p)
  | .var v => wireValue values inputCount gateCount v.index
  | .const c => pure c
  | .add x y => return (← evalExpression values inputCount gateCount x) +
      (← evalExpression values inputCount gateCount y)
  | .mul x y => return (← evalExpression values inputCount gateCount x) *
      (← evalExpression values inputCount gateCount y)

/-- Degree of a substituted wire in its domain-separated challenge base. -/
def wireDegree (inputCount gateCount index : ℕ) : Except String ℕ := do
  if inputVarOffset ≤ index then
    let input := index - inputVarOffset
    if input < inputCount then
      return input + 1
    throw s!"input variable {input} is outside input arity {inputCount}"
  if index ≥ 3 * gateCount then
    throw s!"local variable {index} is outside {gateCount} three-wire gate encodings"
  return index / 3 + 1

/-- Conservative total degree after substituting geometric challenge powers. -/
def expressionDegree {p : ℕ} [Fact p.Prime] (inputCount gateCount : ℕ) :
    Expression (F p) → Except String ℕ
  | .var v => wireDegree inputCount gateCount v.index
  | .const _ => pure 0
  | .add x y => do
      let dx ← expressionDegree inputCount gateCount x
      let dy ← expressionDegree inputCount gateCount y
      return max dx dy
  | .mul x y => do
      let dx ← expressionDegree inputCount gateCount x
      let dy ← expressionDegree inputCount gateCount y
      return dx + dy

/-- Ordinary polynomial degree in the circuit variables, before geometric
challenge substitution. Production `add`, `enforce_zero`, and serialized
outputs are linear and therefore have degree at most one. -/
def variableDegree {F : Type} : Expression F → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add x y => max (variableDegree x) (variableDegree y)
  | .mul x y => variableDegree x + variableDegree y

/-- Require the assertion following gate `g` to be exactly `A_g * B_g - C_g`
in canonical polynomial form. This prevents a nonlinear Lean expression from
collapsing identically under the geometric challenge substitution. -/
def validateGateAssertion {p : ℕ} [Fact p.Prime] (gate : ℕ)
    (assertion : Expression (F p)) : Except String Unit := do
  let expected : Ragu.Fingerprint.Poly p :=
    [([3 * gate, 3 * gate + 1], 1), ([3 * gate + 2], -1)]
  if Ragu.Fingerprint.normalize assertion != expected then
    throw s!"gate {gate} assertion is not the canonical A * B - C relation"

structure ParsedOperations (p : ℕ) where
  gateAssertions : List (Expression (F p))
  constraints : List (Expression (F p))

/-- Decode Clean's current gate representation. A production gate is exactly
one three-wire witness followed immediately by its `A * B - C` assertion.
`encodedDegree` subsequently validates the assertion canonically, and
`evaluatePoint` evaluates its actual value rather than silently replacing it
with an assumed expression. -/
def parseOperations {p : ℕ} [Fact p.Prime] :
    List (FlatOperation (F p)) → Except String (ParsedOperations p)
  | [] => pure ⟨[], []⟩
  | .witness m _ :: rest => do
      if m ≠ 3 then
        throw s!"unsupported witness count {m}; expected a three-wire gate"
      match rest with
      | .assert gate :: tail =>
          let parsed ← parseOperations tail
          return ⟨gate :: parsed.gateAssertions, parsed.constraints⟩
      | _ => throw "a three-wire gate witness was not immediately followed by its gate assertion"
  | .assert constraint :: rest => do
      let parsed ← parseOperations rest
      return ⟨parsed.gateAssertions, constraint :: parsed.constraints⟩
  | .lookup _ :: _ => throw "lookup operations are not supported by polynomial fingerprints"
  | .interact _ :: _ => throw "channel interactions are not supported by polynomial fingerprints"

/-- Check the actual Lean expressions against the structural degree bound that
the production `Driver` API guarantees. This makes nonlinear "linear"
constraints and outputs fail closed instead of silently invalidating the
Schwartz--Zippel accounting. -/
def encodedDegree {p : ℕ} [Fact p.Prime] (inputCount : ℕ)
    (parsed : ParsedOperations p) (outputs : List (Expression (F p))) : Except String ℕ := do
  let gateCount := parsed.gateAssertions.length
  let mut degree := 0
  for (gateAssertion, gate) in parsed.gateAssertions.zipIdx do
    validateGateAssertion gate gateAssertion
    let assertionDegree ← expressionDegree inputCount gateCount gateAssertion
    degree := max degree (gate + 1 + assertionDegree)
    degree := max degree (3 * (gate + 1))
  for (constraint, position) in parsed.constraints.zipIdx do
    if variableDegree constraint > 1 then
      throw s!"constraint {position} is nonlinear outside a production gate"
    let constraintDegree ← expressionDegree inputCount gateCount constraint
    degree := max degree (position + 1 + constraintDegree)
  for (output, position) in outputs.zipIdx do
    if variableDegree output > 1 then
      throw s!"output {position} is nonlinear outside the production Driver model"
    let outputDegree ← expressionDegree inputCount gateCount output
    degree := max degree (position + 1 + outputDegree)
  return degree

def fieldHex {p : ℕ} [Fact p.Prime] (value : F p) : String :=
  Ragu.Fingerprint.Sha256.hexDigest (pushNat256 ByteArray.empty value.val)

def modulusHex (p : ℕ) : String :=
  let le := pushNat256 ByteArray.empty p
  let be := (List.range 32).foldl (fun out i => out.push (le.get! (31 - i))) ByteArray.empty
  Ragu.Fingerprint.Sha256.hexDigest be

structure PointEvaluation where
  gates : String
  constraints : String
  extras : String
  outputs : String

def evaluatePoint {p : ℕ} [Fact p.Prime] (seed : ByteArray) (instanceName : String)
    (point inputCount : ℕ) (parsed : ParsedOperations p)
    (outputs : List (Expression (F p))) : Except String PointEvaluation := do
  let ctx : ChallengeContext p := ⟨seed, instanceName, point⟩
  let bases := ChallengeBases.new ctx
  let gateCount := parsed.gateAssertions.length
  let values := ChallengeValues.new bases inputCount gateCount parsed.constraints.length outputs.length

  let mut gateAccumulator : F p := 0
  for (gateAssertion, gate) in parsed.gateAssertions.zipIdx do
    let ab ← evalExpression values inputCount gateCount gateAssertion
    let c := values.wireC[gate]!
    let d := values.wireD[gate]!
    gateAccumulator := gateAccumulator + values.gateAbWeights[gate]! * ab
    gateAccumulator := gateAccumulator + values.gateCdWeights[gate]! * (c * d)

  let mut constraintAccumulator : F p := 0
  for (constraint, position) in parsed.constraints.zipIdx do
    let value ← evalExpression values inputCount gateCount constraint
    constraintAccumulator := constraintAccumulator +
      values.constraintWeights[position]! * value

  let mut outputAccumulator : F p := 0
  for (output, position) in outputs.zipIdx do
    let value ← evalExpression values inputCount gateCount output
    outputAccumulator := outputAccumulator + values.outputWeights[position]! * value

  return {
    gates := fieldHex gateAccumulator
    constraints := fieldHex constraintAccumulator
    -- No enrolled Lean gadget currently models `assign_extra`; unsupported
    -- witness shapes fail closed in `parseOperations`.
    extras := fieldHex (0 : F p)
    outputs := fieldHex outputAccumulator }

def PointEvaluation.render (point : PointEvaluation) : String :=
  s!"{point.gates},{point.constraints},{point.extras},{point.outputs}"

/-- Maximum number of 512-bit strings that wide modular reduction maps to one
field element. -/
def reductionPreimageBound (fieldSize : ℕ) : ℕ :=
  (2 ^ 512 + fieldSize - 1) / fieldSize

/-- Schwartz--Zippel expression for `points` independent 512-bit random-oracle
outputs, including the small nonuniformity introduced by modular reduction. -/
def schwartzZippelBound (fieldSize degree points : ℕ) : ℚ :=
  (((degree * reductionPreimageBound fieldSize : ℕ) : ℚ) / (2 ^ 512 : ℕ)) ^ points

/-- Numeric security accounting for the Pallas base field. This does not prove
the evaluator's semantic correspondence or model SHA-256 as a random oracle. -/
theorem pastaFp_two_point_prob_le :
    schwartzZippelBound Ragu.Core.Primes.p maxDegreeBound defaultPoints ≤
      (1 : ℚ) / 2 ^ 480 := by
  -- `norm_num` expands closed 512-bit arithmetic; keep the required recursion
  -- depth and power-normalization threshold local to this certificate.
  set_option maxRecDepth 8192 in
    set_option exponentiation.threshold 1024 in
      norm_num [schwartzZippelBound, reductionPreimageBound, Ragu.Core.Primes.p,
        maxDegreeBound, defaultPoints, div_le_iff₀]

/-- Numeric security accounting for the Vesta base field. This does not prove
the evaluator's semantic correspondence or model SHA-256 as a random oracle. -/
theorem pastaFq_two_point_prob_le :
    schwartzZippelBound Ragu.Core.Primes.q maxDegreeBound defaultPoints ≤
      (1 : ℚ) / 2 ^ 480 := by
  -- `norm_num` expands closed 512-bit arithmetic; keep the required recursion
  -- depth and power-normalization threshold local to this certificate.
  set_option maxRecDepth 8192 in
    set_option exponentiation.threshold 1024 in
      norm_num [schwartzZippelBound, reductionPreimageBound, Ragu.Core.Primes.q,
        maxDegreeBound, defaultPoints, div_le_iff₀]

end Ragu.PolynomialFingerprint

open Ragu.PolynomialFingerprint in
/-- Direct randomized evaluation record for a formal instance. The structural
header is exact; only the four field accumulators per point are probabilistic. -/
def Ragu.Core.Statements.FormalInstance.polynomialFingerprint
    (inst : Ragu.Core.Statements.FormalInstance) (instanceName : String)
    (seed : ByteArray) (points : ℕ) : Except String String :=
  letI := inst.pPrime
  letI := inst.InputCircuit
  letI := inst.InputValueProvable
  letI := inst.OutputProvable
  let inputCount := size (Value inst.Input)
  let input : Vector (Expression (F inst.p)) inputCount :=
    .ofFn fun i => var ⟨Ragu.Fingerprint.inputVarOffset + i.val⟩
  let circuit := inst.reimplementation (inst.deserializeInput input)
  let outputs := inst.serializeOutput (circuit.output 0) |>.toList
  do
    if seed.size ≠ 32 then
      throw s!"seed must contain exactly 32 bytes, got {seed.size}"
    if points = 0 then
      throw "polynomial evaluation requires at least one point"
    if inputCount ≥ Ragu.Fingerprint.inputVarOffset then
      throw s!"input length {inputCount} overflows the input variable region"
    let parsed ← parseOperations (circuit.operations 0).toFlat
    let gateCount := parsed.gateAssertions.length
    let bound := degreeBound inputCount outputs.length gateCount parsed.constraints.length 0
    let actualDegree ← encodedDegree inputCount parsed outputs
    if actualDegree > bound then
      throw s!"{instanceName}: encoded expression degree {actualDegree} exceeds structural bound {bound}"
    if bound > maxDegreeBound then
      throw s!"{instanceName}: polynomial degree bound {bound} exceeds maximum {maxDegreeBound}"
    let mut evaluations := []
    for point in List.range points do
      let evaluation ← evaluatePoint seed instanceName point inputCount parsed outputs
      evaluations := evaluation.render :: evaluations
    let renderedEvaluations := String.intercalate ";" evaluations.reverse
    return String.intercalate "\t" [
      formatTag,
      Ragu.Fingerprint.Sha256.hexDigest seed,
      instanceName,
      modulusHex inst.p,
      toString inputCount,
      toString outputs.length,
      toString gateCount,
      toString (2 * gateCount),
      toString parsed.constraints.length,
      "0",
      toString bound,
      toString points,
      renderedEvaluations]
