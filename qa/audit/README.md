# Ragu PR audit integration

The reusable engine lives in [tachyon-zcash/ragu-audit](https://github.com/tachyon-zcash/ragu-audit).
Ragu keeps a small caller workflow, an inert context configuration and optional
repository knowledge here. The workflow pins the engine to a full commit SHA.

Every changed file receives a general correctness review. The engine then chooses
deeper work from the actual change, its consumers and findings. A docs correction
need not run protocol checks; CI, performance and proof changes can select
different questions. [RAGU.md](RAGU.md) is optional domain reference material,
not a mandatory cryptographic checklist for every PR.

[context.json](context.json) names bootstrap context, optional reference files and
the notes file. The engine reads this JSON and its notes from the trusted caller
revision, not the PR's proposed version. A PR cannot relax its own policy or raise
the engine's resource limits. The report records both engine and configuration
revisions, selected focus areas and the reason for their selection.

## Invoke after setup

```sh
gh workflow run audit.yml --repo tachyon-zcash/ragu --ref main -f pull_request=908
```

The **Ragu audit → Run workflow** UI accepts the same PR number. PR events queue
the dedicated App's `ragu-audit/completed` check; manual invocation performs the
review. A new head needs a new review. Completion does not mean findings are
resolved or that code is approved.

## One-time setup

1. Install a dedicated GitHub App on Ragu with **Checks: read/write** and
   **Pull requests: read-only**. Disable webhooks; Actions creates installation
   tokens without a hosted bot service.
2. Create the `ragu-audit-publisher` Actions environment, restricted to deployments
   from **branch `main` only**, without tag rules. Put the App's PEM private key
   in its environment secret `RAGU_AUDIT_APP_PRIVATE_KEY`. Do not put this key in
   repository-wide secrets.
3. Create a separate `ragu-audit-model` environment, also restricted to `main`,
   with an `ANTHROPIC_API_KEY` environment secret. No App key belongs there.
4. Set repository variables `RAGU_AUDIT_APP_ID` (numeric App ID),
   `RAGU_AUDIT_MODEL` (an explicit supported Anthropic model ID), and
   `RAGU_AUDIT_ENABLED=true`. The caller passes the same-named secrets explicitly;
   the reusable jobs select their appropriate environments.
5. Run reviews, inspect the reports and calibrate quality. Then require
   `ragu-audit/completed` in the existing `main` ruleset and select this dedicated
   App as the expected publisher. Keep the other required checks.

Until those steps are complete, this integration is opt-in and does not enable a
merge gate. Once the App check is required, missing or incomplete reviews block
merging. Review findings and their resolution remain a maintainer decision.

The engine reads Git objects and sends tool-free source-review requests to
Anthropic. It executes no PR actions, tests, Cargo build scripts, proc macros or
model-generated commands. Its controller tests establish orchestration behavior;
model quality and authenticated publication require separate validation.

Freshness is checked before publication. For review against the final integrated
tree, also enforce up-to-date branches. The current reusable workflow does not
implement `merge_group`; add a merge-queue adapter before requiring it in a merge
queue. Configured ruleset bypass actors retain their existing powers.

## Update the engine

Review the desired engine revision, then regenerate the caller with its exact
commit using the engine repository's `scripts/render_integration.py`. Update the
single pinned `uses:` reference in `.github/workflows/audit.yml` through a normal
Ragu PR. The engine does not follow a mutable branch or silently upgrade itself.
