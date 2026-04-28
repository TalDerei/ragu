# Introduction

`Clean` is a Lean 4 framework that allows users to define zero-knowledge circuits and prove that they are correct.
Instead of treating circuit code, assumptions, informal comments, and proof obligations as separate artifacts, Clean packages them together in a single formal object.

A circuit in Clean comes with:

- a type description of its inputs and outputs,
- a circuit definition,
- explicit assumptions on the input,
- a formal specification,
- a proof of soundness, and
- a proof of completeness.

At a high level, **soundness** means that any assignment satisfying the circuit constraints also satisfies the circuit specification, assuming some properties about the inputs.
This is the direction that rules out underconstrained circuits.

**Completeness** is the other direction: for inputs satisfying the assumptions, the honest prover can produce a satisfying witness.
This rules out overconstrained circuits, ensuring that an honest prover will always be able to satisfy the circuit.

One of the core concepts in Clean is **compositionality**: once a gadget has been packaged as a verified `FormalCircuit`, it can be used as a subcircuit inside a larger construction together with its properties and proofs.
This lets us build larger verified systems from smaller verified parts instead of reproving everything from scratch.

The following chapters unpack the core pieces of that workflow: the circuit monad used to write circuits, the expression and environment model used to interpret them, the proof structure behind soundness and completeness, and the way verified subcircuits compose.
