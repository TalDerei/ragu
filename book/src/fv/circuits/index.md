# Verified Circuits

The goal of this project is to formally verify properties of Ragu circuits. The
main properties we care about are soundness and completeness, with respect to
stated assumptions and specifications.

As we have explained in the `Clean` section, soundness says that any witness
satisfying the extracted constraints also satisfies the intended specification,
assuming the stated input assumptions. Completeness, on the other hand, says
that for inputs satisfying those assumptions, the honest witness generation
satisfies the constraints.

## Two possible approaches

There are two main ways to connect the Rust implementation to the Lean proof
development that we considered. In both cases, we need to somehow export a
representation of Ragu circuits, generating a Lean definition that makes sense
and is useful for the scope of the verification, and then proving theorems about
that definition.

### Approach 1: export the high-level structure

One option is to extract a higher-level circuit description from the Rust code.
In this style of export, the exported circuit object stays generic:

- constants may remain symbolic,
- compile-time parameters may stay as Lean parameters,
- the extracted object may preserve more of the original circuit structure.

This gives a more general formalization: for example, one may hope to reason
once about a whole circuit family, for all possible compile-time parameters,
rather than about one concrete instantiation.

The cost is that the exporter is complex, and becomes part of a large trusted
interface: it has to preserve the meaning of high-level structure, parameters,
constants, and symbolic circuit composition. That makes the approach more
error-prone, and the trust assumption on the exporter becomes correspondingly
larger.

### Approach 2: export based on a tiny low-level interface

The other option is to trust only a very small export interface: in that style,
the exporter emits concrete low-level operations:

- the prime field is fixed,
- constants are concretized,
- compile-time parameters are instantiated,
- the result is just the exact operation trace and output expressions for that
  concrete circuit instance.

This substantially reduces the trusted interface: the exporter only has to
produce the concrete objects that are directly checked by the proof development.
The cost is that every verified object is a concrete circuit instance rather
than a generic circuit family. It also loses a great deal of structure, so
proving properties directly from the exported low-level trace would be much
harder.

## Chosen approach

This project chooses the second approach. We argue that this is a reasonable
approach:

- In concrete deployments, one usually cares about a small number of actual
  circuit instances, and those instances can be enumerated explicitly. Making
  the prime field and all constants concrete is also desirable, because the
  formalization then talks about exactly what the proof system will verify.
- By exporting only raw low-level operations, the trusted interface becomes much
  smaller. The proof development does not need to trust a complicated
  translation of high-level Rust structure into high-level Lean structure.

## Recovering structure with a reimplementation

The key observation is that one can keep the low-level extracted representation
while recovering high-level structure separately in Lean. For each extracted
instance, the Lean side provides a `reimplementation`: this is an ordinary
`FormalCircuit` in `Clean`, written compositionally out of smaller gadgets, and
it can remain parameterized in the usual Lean style.

The Lean soundness and completeness theorems are proved about this
reimplementation. Applying those theorems to the Rust circuit relies on two
complementary checks. The
[fingerprint equivalence check](./fingerprint.md) requires the concrete `Clean`
reimplementation to emit the same normalized operations and outputs as the
exact three-wire extractor trace. The
[direct randomized polynomial check](./polynomial-fingerprint.md) separately
runs the real gadget through a four-slot production-style driver while Lean
reconstructs the same evaluations from its own model. CI requires both checks
for every instance.

This gives the best of both approaches:

- the trusted extracted object stays concrete and low-level, and never needs to
  be rendered into Lean source code,
- the proof can still use the full compositional structure of `Clean`,
- the actual soundness and completeness arguments are carried out on the
  structured reimplementation, so that proofs are much more manageable,
- the exact and randomized comparisons connect those results back to the Rust
  gadget's driver-level constraint system.

```admonish note
The exact check relies on the principle that identical normalized operations
and outputs describe the same abstract constraint system. The randomized check
tests equality of the corresponding ordered polynomial relations without first
constructing that complete symbolic Rust object. Neither check establishes the
backend layout or final deployed composed circuit; those are separate
refinement obligations.
```

## Maintenance considerations

At first sight, maintaining both an exporter and a Lean reimplementation may
look expensive. In practice, if a circuit changes, the proofs usually need to be
updated anyway. Most of the maintenance cost lies in repairing the proofs, not
in adjusting the reimplementation.

The reimplementation also does not need to mimic the Rust code line by line. It
only needs to produce the same constraint polynomials and outputs — drift in
either direction is caught by the exact and randomized comparisons in CI.
Because of that, it is
a good candidate for partial automation, including LLM-assisted generation, as
long as the digests then match.

## The formal instance interface

The `FormalInstance` object packages a concrete circuit instantiation: the
concrete prime field, the reimplementation, and the serialization glue between
the extractor's flat input/output interface and the reimplementation's
structured types. Its reimplementation field uses
`GeneralFormalCircuit.WithHint` (clean's most general circuit interface), so
ordinary `GeneralFormalCircuit`s are embedded with `.toWithHint`.

At a high level, its fields have the following roles:

- `p` fixes the concrete prime field.
- `deserializeInput` interprets the flat extracted input vector as a structured
  `Input`.
- `serializeOutput` maps a structured `Output` back to the flat extracted output
  vector.
- `reimplementation` is the structured `Clean` `GeneralFormalCircuit.WithHint`
  used for the actual proofs.

The connection to the Rust circuit is not a field of the structure: CI applies
both the exact [fingerprint equivalence check](./fingerprint.md) and the
[direct randomized polynomial check](./polynomial-fingerprint.md) to the
generated registry of formal instances.
