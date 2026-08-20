//! Shared library for the `ragu_testing-fuzz` targets.
//!
//! Holds the generated-program [`substrate`] (op grammar, byte decoder,
//! driver-generic synthesis, native shadow, circuit wrapper) the fuzz
//! targets are built on; the `#[bin]` targets under `fuzz_targets/` depend
//! on this lib. The substrate lives here rather than in `ragu_testing`
//! because the fuzz targets are its only consumers. The patcher engine
//! (recording driver, repair solver, rank oracle, free-advice discovery,
//! playback cross-check) lives in [`ragu_testing::patcher`], where
//! `ragu_pcd`'s own tests can aim it at the internal recursion circuits;
//! `fuzz_advice_patcher` drives it over generated programs.
//!
//! [`params`] holds the fuzzer-chosen field and rank dispatch, so a target
//! can cover `ProductionRank` and both fields of the cycle without paying
//! production-rank cost on every input.
//!
//! [`pcd`] holds what the proof-level targets share: the application
//! fixtures, the honest proof shapes, and the `Arbitrary` vocabulary that
//! decodes fuzzer bytes into a `ragu_pcd::fuzz_utils::Corruption`.

pub mod params;
pub mod pcd;
pub mod substrate;
