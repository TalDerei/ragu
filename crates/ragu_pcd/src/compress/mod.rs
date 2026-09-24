//! Proof compression: the decider's checks restated over commitments and
//! openings, ending in one IPA opening per curve.
//!
//! Built up in stages. The [`claims`] module evaluates the revdot claims
//! from openings, [`revdot`] reduces them to polynomial openings, and
//! [`batch`] combines every opening into the one claim the IPA proves; the
//! compressed proof itself follows.

// Consumed by the compressed prover and verifier once they land.
#![cfg_attr(not(test), allow(dead_code))]

pub(crate) mod batch;
pub(crate) mod claims;
pub(crate) mod revdot;
