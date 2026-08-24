import CompElliptic.Meta.AxiomCheck

/-!
# Ragu trust-assertion machinery

Ragu reuses the hardened `assert_axioms` and `assert_computable` commands from its direct,
commit-pinned CompElliptic dependency. Keeping this project-owned adapter under `Ragu.Meta` makes
the provenance and local trust boundary explicit without maintaining a divergent copy of the
checker.

The upstream implementation checks fully qualified targets, transitive axiom budgets,
`native_decide` ownership, compiled-body overrides, unsafe/partial definitions, and
noncomputability. `Ragu.Meta.EndpointCensus` adds Ragu-specific pin recording and endpoint
discovery around those commands.
-/
