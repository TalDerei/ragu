//! Evaluation domain — re-exported from `ragu_arithmetic::Domain`.
//!
//! Specialized to the mock's field `Fp`. Formerly a self-contained
//! reimplementation; the mock now reuses the real domain directly (identical
//! public API over `pasta_curves::Fp`).

use ragu_pasta::Fp;

/// The mock's evaluation domain: the real [`ragu_arithmetic::Domain`] over the
/// Pallas base field `Fp`.
pub type Domain = ragu_arithmetic::Domain<Fp>;
