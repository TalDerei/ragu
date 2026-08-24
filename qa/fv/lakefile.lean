import Lake
open Lake DSL

package Ragu where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Ragu where
  -- Build every module under `Ragu/`, not just `Ragu.lean`'s import closure, so
  -- a `.lean` that no aggregator imports cannot silently escape CI.
  globs := #[`Ragu.*]

-- Prints the canonical digest of every formal instance's reimplementation;
-- CI compares the output against `cargo run -p lean_extraction -- fingerprint`.
lean_exe fingerprints where
  root := `Ragu.Fingerprint.Main

-- Clean's last upstream Lean 4.30 revision, immediately before its 4.31 bump.
-- Keep this independent of Ironwood's later Clean pin and API migrations.
require clean from git "https://github.com/Verified-zkEVM/clean" @
  "03e41e980d789a761840fc62b955b689a60223c4"

-- Upstream Pasta curve and field proofs used directly by Ragu.
require CompElliptic from git "https://github.com/daira/CompElliptic" @
  "2c0444035a84db957f27f06433715058d1e890ad"

-- Keep mathlib last so its toolchain-matched common transitive dependencies
-- take precedence over CompElliptic's CompPoly dependency graph.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"
