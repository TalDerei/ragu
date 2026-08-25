# Gate logic for the `ci-required` aggregate job in rust.yml.
#
# Input: the `needs` context (`toJSON(needs)`), i.e.
#   { "<job>": { "result": "success" | "failure" | "cancelled" | "skipped",
#                "outputs": { ... } } }
# Argument: `$event`, the workflow event name.
#
# A job is *gated* when the `changes` outputs (or a push) would have run it. A
# gated job must report `success`; an ungated job may be skipped but must not
# have failed or been cancelled. Emits one line per offending job, so empty
# output means the gate passes. A job listed here but absent from `needs` is
# reported as `missing`, and a job present in `needs` but absent here as
# `unlisted`, so the two lists cannot drift apart in either direction.
. as $needs
| ($needs.changes.outputs // {}) as $c
| ($event == "push") as $push
| ($push or $c.rust == "true") as $rust
| ($push or $c.book == "true") as $book
| ($rust or $c.fuzz == "true") as $fuzz
| ($rust or $c.supply == "true") as $supply
| [
    {name: "changes",        gated: true},
    {name: "tier-mix",       gated: false},
    {name: "fmt",            gated: $rust},
    {name: "clippy",         gated: $rust},
    {name: "backend-equivalence", gated: $rust},
    {name: "mock",           gated: $rust},
    {name: "proptests-fast", gated: $rust},
    {name: "test",           gated: $rust},
    {name: "test-32-bit",    gated: $rust},
    {name: "build-nostd",    gated: $rust},
    {name: "bitrot",         gated: $rust},
    {name: "backend-boundary", gated: $rust},
    {name: "backend-perf",   gated: ($event == "pull_request" and $c.acceleration == "true")},
    {name: "fuzz-check",     gated: $fuzz},
    {name: "docs",           gated: $rust},
    {name: "book",           gated: $book},
    {name: "vet",            gated: $supply},
    {name: "audit",          gated: $supply}
  ]
| . as $rows
| ($rows | map(.name)) as $listed
# A job in `needs:` without a row here would otherwise be invisible to the
# gate, so an unlisted job is an error regardless of its result.
| (($needs | keys) - $listed
   | map({name: ., result: $needs[.].result, gated: "unlisted"})) as $unlisted
| ($rows | map(. + {result: ($needs[.name].result // "missing")}))
| map(select(
    (.gated == true and .result != "success")
    or .result == "failure" or .result == "cancelled" or .result == "missing"))
| . + $unlisted
| .[]
| "\(.name): \(.result) (gated: \(.gated))"
