# Targets

The catalog of fuzz targets: what each one generates, what it asserts, and
where it sits relative to the [oracle families](oracles.md). The authoritative
per-target reference is `qa/fuzz/README.md`; this chapter should give the
reader the shape of the coverage rather than restate it.

## Planned contents

- **The shared substrate.** The op grammar, the total byte decoder with
  decode-time clamping, per-op capability flags and `OpSet` masks, and the
  proptest strategies that let in-tree property tests run over the same
  abstract syntax under plain `cargo test`. This is the piece that makes the
  corpora interchangeable, and it belongs first.

- **Op-stream targets.** Random gadget compositions over `Element` and
  `Boolean`: the robustness workhorse, a witness-state-hash variant that biases
  the search toward distinct internal states, a mid-stream substitution target,
  and the driver differential.

- **Soundness and patcher targets.** The under-constraint family over generated
  circuits — trace-coefficient mutation against the revdot identity, witness
  mutation with re-tracing, and advice mutation repaired through a captured
  constraint graph.

- **Gadget-API property targets.** Algebraic identities on the gadget surface,
  assertion gadgets accepting and rejecting correctly, bit packing round-trips,
  the `Consistent` invariants, and serialization round-trips.

- **Primitive-level targets.** Poseidon sponge sequences and the native-versus-
  circuit differential, endoscalar operations, the reverse-dot-product
  primitive and its folding, and registry consistency for $s(X, Y)$.

- **Circuit-pipeline targets.** The higher-layer targets that drive full
  witness, evaluation, and assembly pipelines rather than calling gadgets
  directly, including the staging system's per-stage and combined invariants.

- **Verifier robustness.** Corrupted proof bytes against the verifier.

## Coverage gaps

A catalog is most useful when it says what is missing. This chapter should
close by naming the parts of the system no target currently generates, so that
the list of targets is read as a map with edges rather than as a claim of
completeness.
