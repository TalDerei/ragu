//! Proof compression: the decider's checks restated over commitments and
//! openings, ending in one IPA opening per curve.
//!
//! Built up in stages. The [`claims`] module evaluates the revdot claims
//! from openings, and [`revdot`] reduces them to polynomial openings; the
//! batch that combines the openings and the compressed proof itself follow.

// Consumed by the compressed prover and verifier once they land.
#![cfg_attr(not(test), allow(dead_code))]

pub(crate) mod claims;
pub(crate) mod revdot;
