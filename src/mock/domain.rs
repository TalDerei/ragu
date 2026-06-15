//! Evaluation domain — re-exported from `ragu_arithmetic::Domain`.
//!
//! Specialized to the mock's legacy field `Fp`. Formerly a self-contained
//! reimplementation; the mock now reuses the real domain directly (identical
//! public API, and the same legacy `pasta_curves::Fp` under `legacy-deps`).

use pasta_curves::Fp;

/// The mock's evaluation domain: the real [`ragu_arithmetic::Domain`] over the
/// legacy field `Fp`.
pub type Domain = ragu_arithmetic::Domain<Fp>;
