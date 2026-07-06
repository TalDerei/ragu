//! Evaluation domain — re-exported from `ragu_arithmetic::Domain`.
//!
//! Specialized to the mock's field `Fp`. Formerly a self-contained
//! reimplementation; the mock now reuses the real domain directly (identical
//! public API, over whichever `pasta_curves::Fp` the active crypto stack
//! selects).

use ragu_pasta::Fp;

/// The mock's evaluation domain: the real [`ragu_arithmetic::Domain`] over the
/// Pallas base field `Fp`.
pub type Domain = ragu_arithmetic::Domain<Fp>;
