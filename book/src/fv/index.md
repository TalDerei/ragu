# Scope

Ragu's soundness rests on its circuits constraining exactly what they are meant
to constrain. A gadget that assigns a wire but never constrains it still
produces proofs that verify, and nothing in the prover objects, because an
honest prover never exercises the gap. Tests sample the input space and
[fuzzing](../fuzzing/index.md) searches it, but a search that finds nothing has
not shown that there is nothing to find. A machine-checked proof has.

This part documents that proof effort: the framework the proofs are written in,
how a Rust circuit is connected to a Lean theorem about it, and — because this
matters more than the theorems themselves — what those theorems do and do not
say. The work is carried out with
[Clean](https://github.com/Verified-zkEVM/clean), a Lean 4 framework for
zero-knowledge circuits developed by the Verified zkEVM project, in
collaboration with [zkSecurity](https://zksecurity.xyz/).

## Two properties

Every verified circuit carries a proof of two properties, stated against
explicit assumptions on its inputs and an explicit specification of its
intended behavior.

**Soundness** says that any witness satisfying the circuit's constraints also
satisfies the specification. This is the direction that rules out
under-constrained circuits, and it is the direction a malicious prover attacks.

**Completeness** says that for inputs satisfying the assumptions, an honest
prover can always produce a satisfying witness. This rules out over-constrained
circuits, which are a liveness problem rather than a soundness one.

Both are conditional on the assumptions, and an assumption the caller does not
actually establish is a hole in the argument rather than a detail. The
[assumptions](circuits/assumptions.md) chapter is the honest accounting of
those conditions, and it is the chapter to read before quoting any result from
this part.

## What is verified today

Verification currently covers the gadget layer: 49 concrete circuit instances,
each one a specific instantiation at a fixed prime field with all compile-time
parameters made concrete.

- **Field elements** — multiplication, squaring, allocation, inversion,
  division by a nonzero element, zero and equality tests, root-of-unity
  enforcement, invertible allocation and enforcement, and folding at six
  arities.
- **Curve points** — allocation on both curves of the cycle, doubling,
  incomplete addition, incomplete double-and-add, and conditional
  endomorphism application and negation.
- **Booleans** — allocation, conjunction, conditional selection, and
  conditional equality enforcement.
- **Endoscalars** — allocation, extraction, lifting, and group scaling.
- **Poseidon** — the permutation at the deployed Pasta parameters on both
  fields, and the sponge: single-block hashing on each field, and a
  two-block, three-squeeze shape that crosses a rate boundary.
- **Horner evaluation** at three arities, plus the trailing-constant $k(Y)$
  form.
- **Nonzero banks** at three arities, and the core multiplication gate.

Every one of these is proved without `sorry`, and the Lean build runs with
`--wfail` so that an admitted goal fails CI rather than passing quietly. The
axioms each theorem depends on can be listed with `#print axioms`; the
assumptions chapter records which ones appear and what trusting them costs.

## What is not verified

Everything above the gadget layer. The internal recursion circuits, the
accumulation scheme, the staging system, and the protocol as a whole have no
Lean theorems about them.

Some of the gadget layer has nothing to verify rather than something unproved,
and the distinction matters when reading the list above as a coverage claim.
Demotion (`promotion.rs`) strips witness data through a driver whose every
method is unreachable, the serialization surface (`io.rs`) moves wires without
emitting constraints, and the `Consistent` trait only delegates — the
constraints its implementations re-emit belong to the gadgets themselves, and
for `Nonzero` and `Invertible` those are the invertible-allocation instances
above. A reimplementation of any of these would prove a theorem about no
constraints. What they are not exempt from is *trust*: the extractor relies on
this serialization to read wires in and out, so a bug there would change what
every other theorem is about.

Neither is any Rust code verified: the proofs are about
circuits extracted from Rust, not about the Rust implementation that extracted
them, and not about the prover and verifier that run the protocol. The
cryptographic assumptions underlying the construction are out of scope by
construction — no proof assistant establishes that the discrete logarithm
problem is hard.

The [assumptions](circuits/assumptions.md) chapter states these boundaries
precisely, including the ways a gap between the formalization and reality makes
a theorem inapplicable rather than merely approximate.

## How the connection is made

Rust circuits and Lean proofs are joined without either side being translated
into the other. A driver runs the Rust circuit and records the low-level
operations it emits, giving a concrete trace of witness allocations and
assertions. Separately, the circuit is reimplemented in Clean, compositionally
and in idiomatic Lean, and the soundness and completeness theorems are proved
about that reimplementation. The two are tied together by a digest: both sides
hash their operation trace and output expressions under a canonical encoding,
and CI fails if the digests disagree.

The payoff is a small trusted interface. The exported artifact never has to be
rendered into Lean source, the proofs get the full compositional structure of
Clean to work with, and drift in either direction is caught mechanically. The
[Clean](clean/index.md) chapter covers the framework; the
[verified circuits](circuits/index.md) chapter covers extraction, the digest
check, and the CI wiring.

## Where this is going

The gadget layer is the foundation for the result that matters: **one layer of
recursion**. Verifying a step circuit that verifies a proof is qualitatively
harder than verifying a multiplication gadget, since the specification is
itself a statement about the proof system, and it is the point at which formal
verification starts to say something about Ragu as a recursive proof system
rather than about its parts.

Beyond that sits an open question about what the security model should even be.
Knowledge soundness for PCD is argued by exhibiting an extractor that recovers
a witness from a convincing prover, and the cost of that extractor grows with
recursion depth — an extractor exponential in the depth is a real bound, but a
weak one. Mina addressed this by adopting
[chain extractability](https://minaprotocol.com/wp-content/uploads/technicalWhitepaper.pdf),
a weaker but more practical model than full knowledge soundness. Whether Ragu
should follow, or whether straightline extraction gives a tighter bound, is
undecided; the answer changes what a formalization of recursion should be
proving.

```admonish note
The knowledge extractor of the security argument and the extraction driver of
the next chapter are unrelated things that share a name. The former is a
hypothetical algorithm in a soundness proof; the latter is a Rust driver that
logs circuit operations.
```
