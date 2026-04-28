# Introduction

The goal of this project is to formally verify properties of Ragu circuits.
The main properties we care about are soundness and completeness, with respect to stated assumptions and specifications.

As we have explained in the `Clean` section, soundness says that any witness satisfying the exported constraints also satisfies the intended specification, assuming the stated input assumptions.
Completeness, on the other hand, says that for inputs satisfying those assumptions, the honest witness generation satisfies the constraints.

## Two possible approaches

There are two main ways to connect the Rust implementation to the Lean proof development that we considered.
In both cases, we need to somehow export a representation of Ragu circuits, generating a Lean definition that makes sense and is useful for the scope of the verification, and then proving theorems about that definition.

### Approach 1: export the high-level structure

One option is to extract a higher-level circuit description from the Rust code.
In this style of export, the exported circuit object stays generic:

- constants may remain symbolic,
- compile-time parameters may stay as Lean parameters,
- the extracted object may preserve more of the original circuit structure.

This gives a more general formalization: for example, one may hope to reason once about a whole circuit family, for all possible compile-time parameters, rather than about one concrete instantiation.

The cost is that the exporter is complex, and becomes part of a large trusted interface: it has to preserve the meaning of high-level structure, parameters, constants, and symbolic circuit composition.
That makes the approach more error-prone, and the trust assumption on the exporter becomes correspondingly larger.

### Approach 2: export based on a tiny low-level interface

The other option is to trust only a very small export interface: in that style, the exporter emits concrete low-level operations:

- the prime field is fixed,
- constants are concretized,
- compile-time parameters are instantiated,
- the result is just the exact operation trace and output expressions for that concrete circuit instance.

This substantially reduces the trusted interface: the exporter only has to produce the concrete objects that are directly checked by the proof development.
The cost is that every verified object is a concrete circuit instance rather than a generic circuit family.
It also loses a great deal of structure, so proving properties directly from the exported low-level trace would be much harder.

## Chosen approach

This project chooses the second approach.
We argue that this is a reasonable approach:

- In concrete deployments, one usually cares about a small number of actual circuit instances, and those instances can be enumerated explicitly. Making the prime field and all constants concrete is also desirable, because the formalization then talks about exactly what the proof system will verify.
- By exporting only raw low-level operations, the trusted interface becomes much smaller. The proof development does not need to trust a complicated translation of high-level Rust structure into high-level Lean structure.

## Recovering structure with a reimplementation

The key observation is that one can keep the low-level exported representation while recovering high-level structure separately in Lean.
For each exported instance, the Lean side provides a `reimplementation`: this is an ordinary `FormalCircuit` in `Clean`, written compositionally out of smaller gadgets, and it can remain parameterized in the usual Lean style.

The formal verification statements do not trust the reimplementation, but the user proves that the concrete instantiation of the `Clean` reimplementation **emits exactly the same operations and output expressions as the exported circuit instance**.

This gives the best of both approaches:

- the trusted exported object stays concrete and low-level,
- the proof can still use the full compositional structure of `Clean`,
- the actual soundness and completeness arguments are carried out on the structured reimplementation, so that proofs are much more manageable,
- the equality proofs connect those results back to the exported circuit.

> [!NOTE]
> This approach relies on one important principle: circuits that produce the same exact operations and the same exact outputs are equivalent.
> This is quite easy to see: if the operations are identical, the two circuits make the same exact allocations, enforce the same exact constraints and emit the same exact outputs.
> That is why we prove properties about the `Clean` reimplementation rather than reasoning directly over the raw exported trace.

## Maintenance considerations

At first sight, maintaining both an exporter and a Lean reimplementation may look expensive.
In practice, if a circuit changes, the proofs usually need to be updated anyway.
Most of the maintenance cost lies in repairing the proofs, not in adjusting the reimplementation.

The reimplementation also does not need to mimic the Rust code line by line.
It only needs to produce the same operations and outputs.
Because of that, it is a good candidate for partial automation, including LLM-assisted generation, as long as the equality proofs are then completed in Lean.

## The `FormalInstance` interface

The `FormalInstance` object packages a concrete exported circuit instantiation, together with the reimplementation, and proofs about it.

Intuitively, the definition of a `FormalInstance` will provide:

- the concrete exported circuit interface,
- the structured Lean interpretation of that interface,
- the Clean reimplementation we want to reason about,
- the assumptions and specification for this concrete instance,
- and the proofs that the reimplementation matches the exported circuit exactly.

At a high level, its fields have the following roles:

- `p` fixes the concrete prime field.
- `inputLen` and `outputLen` fix the flat arities of the exported interface.
- `exportedOperations` is the low-level operation trace produced by extraction.
- `exportedOutput` is the low-level vector of output expressions produced by extraction.
- `Input` and `Output` are the structured Lean input/output types used for reasoning.
- `deserializeInput` interprets the flat exported input vector as a structured `Input`.
- `serializeOutput` maps a structured `Output` back to the flat exported output vector.
- `Assumptions` and `Spec` are the assumptions and intended property stated for this concrete instance.
- `reimplementation` is the structured `Clean` `FormalCircuit` used for the actual proofs.
- `same_circuit` proves that the reimplementation emits exactly the exported operations.
- `same_output` proves that the reimplementation returns exactly the exported outputs, after serialization.
- `same_spec` proves that the instance specification agrees with the specification of the reimplementation.
- `same_assumptions` proves that the instance assumptions agree with the assumptions of the reimplementation.

> TODO: adjust later for completeness
