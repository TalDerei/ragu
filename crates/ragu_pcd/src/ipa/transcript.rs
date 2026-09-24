//! What the IPA needs from a transcript.

use ragu_arithmetic::CurveAffine;
use ragu_core::Result;

/// What the IPA needs from a transcript: halo2's `TranscriptWrite`
/// operations, with the proof carried as a struct rather than written to a
/// byte stream, so the verifier writes what the prover wrote.
pub trait IpaTranscript<C: CurveAffine> {
    /// Absorbs a point.
    fn write_point(&mut self, point: C) -> Result<()>;

    /// Absorbs a scalar.
    fn write_scalar(&mut self, scalar: C::Scalar) -> Result<()>;

    /// Squeezes a challenge in the scalar field.
    fn squeeze_challenge(&mut self) -> Result<C::Scalar>;
}
