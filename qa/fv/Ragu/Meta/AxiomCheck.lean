import CompElliptic.Meta.AxiomCheck

/-!
# Ragu trust-assertion machinery

Ragu reuses the hardened `assert_axioms` and `assert_computable` commands from its direct,
commit-pinned CompElliptic dependency: `CompElliptic/Meta/AxiomCheck.lean` at commit
`2c0444035a84db957f27f06433715058d1e890ad`. That checker is the synchronized adaptation of
Ironwood's `Zcash/Meta/AxiomCheck.lean`; keeping this project-owned adapter under `Ragu.Meta` makes
the provenance and local trust boundary explicit without maintaining another divergent copy.

The upstream implementation checks fully qualified targets, transitive axiom budgets,
`native_decide` ownership, compiled-body overrides, unsafe/partial definitions, and
noncomputability. `Ragu.Meta.EndpointCensus` adds Ragu-specific pin recording and endpoint
discovery around those commands.
-/
