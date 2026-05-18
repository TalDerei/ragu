import Lake
open Lake DSL

package Ragu where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxHeartbeats, (4000000 : Nat)⟩,
    ⟨`maxRecDepth, (2000 : Nat)⟩]

@[default_target]
lean_lib Ragu where

require clean from git "https://github.com/Verified-zkEVM/clean" @ "main"
