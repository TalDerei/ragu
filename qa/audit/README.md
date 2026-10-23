# Ragu PR audit

Ragu uses the standalone [ragu-audit](https://github.com/tachyon-zcash/ragu-audit)
engine for change-aware AI source reviews. Every changed file gets a general
review; deeper checks follow the risks of that particular PR.

Start a review by posting `/ragu-audit` as a new PR conversation comment
(requires write access).

[context.json](context.json) supplies project context, and [RAGU.md](RAGU.md)
provides optional cryptographic reference knowledge. These are read from the
trusted configuration revision.

A completed check records that the review finished. Maintainers assess findings
and approve changes.

[Setup guide](https://github.com/tachyon-zcash/ragu-audit/blob/main/docs/integration.md).
