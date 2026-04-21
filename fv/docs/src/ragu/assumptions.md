# Assumptions
## Assumptions for the Ragu Formal Verification to be mathematically meaningful

The Ragu Formal Verification relies on some assumptions.

- The extraction is correct
    - The semantics of the Ragu Driver operations are correctly captured, and are correctly translated into Clean operations (i.e., the exported operations and the Ragu circuit are semantically equivalent)
    - The inputs/outputs serialization is done correctly and done deterministically
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
Also, any gaps between the requirements and the formalizatioon can render the Ragu Formal Verification to be useless.

Lean and other proof assistants that are based on intuitionistic and classical logic suffer from a problem called [explosivity](https://plato.stanford.edu/archives/fall2017/entries/logic-paraconsistent/). From a contradiction about any topic, it is possible to prove all true and false statements. For this reason, when any one of arguments or hypotheses is false, a theorem in Lean does not carry any guarantees.

Because of explosivity, approximations do not work well with Lean and other proof assistants. Just because a situation looks close to satisfy the hypotheses of a theorem, that doesn't mean that the situation is close to satisfy the conclusion of the theorem. The logic behind Lean and other proof assistants does not have the notion of degree of falsehood so any tiny gap between the reality and the formalization can be used to prove things that are utterly wrong.

It is difficult to list all potential gaps between the reality and the formalization. The same holds for potential gaps between the requirements and the formalization. The potential gaps listed are just some typical examples and not to be taken as exhaustive.

Future changes might introduce new gaps.

Anything other than the verified circuit is out of scope. Everything in the Rust source, the Rust compiler, the hardware, and the physical and social level is out of scope. The mathematical theory behind the protocol is mostly out of scope. For example, the cryptographic reductions and the cryptographic assumptions are out of scope. The Rust implementation might behave in a nondeterministic way so that it might sometimes or always use different constraints from the constraints that it exports.

All assumptions in the Lean need to be satisfied by the reality. For this, every argument and every hypothesis of the Lean theorem needs to correspond to a single value that exists or a proposition that holds. Otherwise, the Lean theorem is not applicable. If the theorem is applicable to the reality, the conclusion of the theorem holds for the arguments that satisfy the arguments and the hypotheses of the Lean theorem.

Logically speaking, events in the past do not imply similar events happen in the future, so there is a possibility that the laws of physics do not hold. Assuming the laws of physics for the sake of explanation, electrical computers consume electricity and produce heat so that internal events of electrical computers can be highly predictable out of vastly many possibilities. It is just because of this special environment that very complicated logical formulas seem to describe events in the electrical computers. It is out of scope of any logical system to determine whether a statement is satisfied or not given a set of events. If that kind of interpretation is in place, only when the assumptions made in the logical system are satisfied, proofs in the logical system are meaningful.

The completeness theorem in the Ragu Formal Verification does not guarantee that the honest prover implementation does produce a proof that passes the verification.

If values in the circuit are copied or used somewhere else, the Ragu Formal Verification results are not applicable to the copied and used value in the new context (it's likely that the new context needs to constrain the copied value).

The Ragu Fromal Verification might not be applicable because of missing constraints on the inputs and the outputs of the circuit. The verifier needs to be sure of the Lean assumptions of the circuit soundness without relying on the circuit. The prover needs to be sure of the Lean assumptions of the circuit completeness without relying on the circuit.

The field values in the implementation need to correspond to the field values in the Lean formalization always in the same way. 

The implementation of the circuit satisfiability needs to be sound and complete for the Ragu Formal Verification to be useful. The soundness and completeness of the backend proof system (both theory and implementation) are required. Bugs in libraries, Fiat-Shamir issues (hash function is not random oracle, forgetting transcript elements for Fiat-Shamir), bugs in the prover & verifier implementations, incorrect compilation of the circuit, incorrect field arithmetics, bugs in the Rust compiler, bugs in the Rust source code, hardware bugs, issues around using GPUs (the list is not exaustive) can all render the Ragu Formal Verification to be useless.

Issues in deployment and integration can render the Ragu Formal Verification useless. Availability or integrity issues in the prover or the verifier in software, hardware, building, energy supply, network connectivity or operations, can render the Ragu Formal Verification useless. The same can be said for communication between the prover and the verifier, and the system that use the result that the verifier produces. The result of formal verification is not useful when the user of the prover fails to identify the honest prover implementation with the correct public key, or when the system that uses the result of the verifier fails to identify the verifier implementation with the correct verification key. UI issues can bypass Ragu Formal Verification results.

Ragu Formal Verification does not cover issues in the protocol design. Ragu Formal Verification results do not address MEV, front-running, replay attacks or similar issues.
