# SNARKs

A **succinct non-interactive argument of knowledge (SNARK)** is a
cryptographic proof system that allows a prover to convince a verifier
that a statement is true. The key properties are:

- **Succinct**: the proof is small (much smaller than the computation
  it attests to) and fast to verify.
- **Non-interactive**: the prover sends a single message to the
  verifier; no back-and-forth is needed.
- **Argument of knowledge**: the prover not only demonstrates that a
  valid witness _exists_, but that they actually _know_ one.

SNARKs are the building blocks of
[proof-carrying data](../concepts/pcd.md): each step in a PCD
computation produces a proof that attests to the correctness of that
step, and recursive composition allows these proofs to reference each
other.

## NARKs

A **NARK** (non-interactive argument of knowledge) relaxes the
succinctness requirement on the full proof. In Ragu's split form, the
proof has two parts: a succinct _instance_ that the verifier checks, and
a potentially linear-size _witness_ that only the prover and decider
need. The instance is small and fast to verify; the witness is not.

This relaxation matters for recursive proof composition. A full SNARK
requires the prover to produce a succinct proof at every recursive step,
which is expensive. A NARK defers that cost: the prover carries the
proof witness forward in uncompressed form and only compresses at the
boundary where the proof leaves the recursive pipeline. The
[split-accumulation](../protocol/core/accumulation/index.md) technique
makes this practical — the recursive verifier only processes the
succinct instance, and the witness is accumulated without compression.

Ragu's internal proof system is a NARK. Its instance contains
commitments, evaluation claims, and the IPA accumulator state. Its
witness contains the full polynomial vectors and auxiliary data needed
by the decider. When proofs leave the recursive pipeline, they can be
[compressed](../concepts/pcd.md) to a succinct form for transmission.

## Trusted setup

SNARKs differ in whether they require a _trusted setup_: a one-time
ceremony that produces structured reference parameters. If the secret
randomness from the ceremony leaks, soundness breaks and an adversary
could forge proofs.

- **Pairing-based SNARKs** (Groth16, PlonK with KZG) require a trusted
  setup. In exchange, they achieve constant-size proofs and
  constant-time verification.
- **IPA-based systems** (Bulletproofs, Halo, Ragu) require no trusted
  setup. The commitment scheme uses only a set of independent group
  generators, which can be derived deterministically. Verification is
  linear-time, but accumulation avoids paying that cost at every
  recursive step.

Ragu targets deployment in Zcash as part of
[Project Tachyon](https://tachyon.z.cash/), where avoiding a trusted
setup is a hard constraint. The Pasta curves are not
pairing-friendly, which rules out pairing-based commitments
entirely and limits us to the IPA-based approach.

## Security assumptions

Ragu's security rests on:

- The **elliptic-curve discrete logarithm problem (ECDLP)** on the
  Pasta curves.
- The
  [**discrete log relation assumption**](../protocol/prelim/assumptions.md#ecdlp),
  a stronger variant that underlies the binding property of
  Pedersen vector commitments.
- The **random oracle model**, instantiated with
  [Poseidon](https://eprint.iacr.org/2019/458) for Fiat-Shamir
  transformations.

Knowledge soundness, the guarantee that a convincing prover
_knows_ a valid witness, relies on a
[knowledge assumption](../protocol/prelim/assumptions.md#knowledge-soundness)
for the polynomial commitment scheme.
