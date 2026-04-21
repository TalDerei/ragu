# Assumptions
## Assumptions for the Ragu Formal Verification to be mathematically meaningful

The Ragu Formal Verification relies on some assumptions.

- The extraction is correct
    - The semantics of the Ragu Driver operations are correctly captured, and are correctly translated into Clean operations (i.e., the exported operations and the Ragu circuit are semantically equivalent)
    - The inputs/outputs serialization is done correctly and done deterministically
    - The Rust extraction and Lean extraction use the same ordering of elements during serialization of structures
    - The circuit instance is defined correctly and is coherent with the goal of the FV

- The assumptions and specification properties suffice to fully characterize the circuit within the scope of the FV (e.g., we could prove a Spec that does not imply some real-world broader property we care about)

- The lean "core" statements are correct
    - The same circuit/same output theorem statements suffice to fully characterize semantic equivalence of circuits
    - more generally, the formal instance in lean is correct
    - the Clean core statements about circuit semantics and subcircuit composition are correct
    - the Lean elaborater creates an internal representation of the statement (to be checked together with the proof term by the Lean kernel) in a way that keeps the correct intention

- The logical foundation is not contradictory
    - The Lean kernel theory and implementation are sound.
    - The axioms we use do not turn false propositions to be provable. After a theorem, the command `#print axioms <theoremName>` prints the axioms the theorem transitively depends on. Typically the axioms reported are `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`, and `Ragu.Core.Primes.p_prime`. There is a chance that `Lean.trustCompiler` and `Lean.ofReduceBool` can be used to prove falsehood, so there is a possibility that these axioms are used somewhere to prove something that is not true. Moreover, it is unknown whether the commonly used axioms `propext`, `Classical.choice`, and `Quot.sound` can be used to prove falsehood.

## Assumptions for the Ragu Formal Verification to be useful

Any gaps between the reality and the formalization can render the Ragu Formal Verification to be useless.
Also, any gaps between the requirements (documented or undocumented, or even those not thought about consciously) and the formalization can render the Ragu Formal Verification to be useless.

Lean and other proof assistants that are based on intuitionistic and classical logic suffer from a problem called [explosivity](https://plato.stanford.edu/archives/fall2017/entries/logic-paraconsistent/). From a contradiction about any topic, it is possible to prove all true and false statements. For this reason, when any one of arguments or hypotheses is false, a theorem in Lean does not carry any guarantees.

Because of explosivity, approximations do not work well with Lean and other proof assistants. Just because a situation looks close to satisfy the hypotheses of a theorem, that doesn't mean that the situation is close to satisfy the conclusion of the theorem. The logic behind Lean and other proof assistants does not have the notion of degree of falsehood so any tiny gap between the reality and the formalization can be used to prove things that are utterly wrong. If a situation doesn't satisfy any single hypothesis in a Lean theorem, the Lean theorem doesn't apply to the situation.

It is difficult to list all potential gaps between the reality and the formalization. The same holds for potential gaps between the requirements and the formalization. The potential gaps listed are just some typical examples and not to be taken as exhaustive.

Future changes might introduce new gaps.

Anything other than the verified circuit is out of scope. Everything in the Rust source, the Rust compiler, the hardware, and the physical and social level is out of scope of formal verification. The mathematical theory behind the protocol is mostly out of scope. For example, the cryptographic reductions and the cryptographic assumptions are out of scope. The Rust implementation might behave in a nondeterministic way so that it might sometimes or always use different constraints from the constraints that it exports.

The completeness theorem in the Ragu Formal Verification does not guarantee that the honest prover implementation does produce a proof that passes the verification. The Ragu Formal Verification does not prove any theorems about the Rust implementation of anything, so the prover implementation is not verified. The completeness results in Ragu Formal Verification just talk about the `witness` operations in the Lean code. The Lean `witness` operations are not compared against extractions from Rust.

If values in the circuit are copied somewhere else, the soundness theorems of the Ragu Formal Verification results doesn't tell the verifier anything about the copied values.

The Ragu Formal Verification might not be applicable because of missing constraints on the inputs and the outputs of the circuit. The verifier needs to be sure of the Lean assumptions of the circuit soundness without relying on the circuit. The prover needs to be sure of the Lean assumptions of the circuit completeness without relying on the circuit.

The Lean theorems talk about field elements. In order to use the Lean theorems to reason about the implementation, the field elements in Lean need to correspond to field elements in the implementation. The field elements in the implementation might exist verbatim in the memory (of the prover or the verifier), in the network, or only conceptually accessible through commitment schemes. When the same variable is used multiple times in a Lean statement, all occurrences of the same variables need to correspond to the same field element in the implementation.

The implementation of the circuit proof system (both theory and implementation) needs to be sound for the soundness result of Ragu Formal Verification to be useful.

The completeness result of Ragu Formal Verification has similar limitations. Moreover, since the completeness result is only useful when it's combined with availability of the whole system including the prover, the verifier, the communication between them and actors who operate on these.

Issues in deployment and integration can render the Ragu Formal Verification useless. Availability or integrity issues in the prover or the verifier in software, hardware, building, energy supply, network connectivity or operations, can render the Ragu Formal Verification useless. The same can be said for communication between the prover and the verifier, and the system that use the result that the verifier produces. The result of formal verification is not useful when the user of the prover fails to identify the honest prover implementation with the correct public key, or when the system that uses the result of the verifier fails to identify the verifier implementation with the correct verification key. UI issues can bypass Ragu Formal Verification results.

Ragu Formal Verification does not cover issues in the protocol design. Ragu Formal Verification results do not address MEV, front-running, replay attacks or similar issues.
