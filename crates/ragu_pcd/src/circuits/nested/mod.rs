use arithmetic::Cycle;
use ragu_circuits::{
    CircuitExt,
    mesh::MeshBuilder,
    polynomials::Rank,
    staging::{StageExt, Staged},
};
use ragu_core::Result;
use ragu_primitives::vec::Len;

use crate::components::endoscalar::{EndoscalarStage, EndoscalingStep, NumStepsLen, PointsStage};
use crate::proof::NUM_P_COMMITMENTS;

/// Index of internal nested circuits registered into the mesh.
///
/// These correspond to the circuit objects registered in [`register_all`].
/// The `EndoscalingStepStart` variant marks where the dynamically registered
/// `EndoscalingStep` circuits begin; individual steps can be indexed as
/// `EndoscalingStepStart as usize + step_index`.
#[derive(Clone, Copy, Debug)]
#[repr(usize)]
pub(crate) enum InternalCircuitIndex {
    // Stages
    /// `EndoscalarStage` stage object
    EndoscalarStage = 0,
    /// `PointsStage` stage object
    PointsStage = 1,
    // Final stage objects
    /// `PointsStage` final staged object
    PointsFinalStaged = 2,
    // Marker for dynamically registered EndoscalingStep circuits
    /// Start index for `EndoscalingStep` circuits (indices 3+)
    EndoscalingStepStart = 3,
}

pub mod stages;

/// Register internal nested circuits into the provided mesh.
pub(crate) fn register_all<'params, C: Cycle, R: Rank>(
    mut mesh: MeshBuilder<'params, C::ScalarField, R>,
) -> Result<MeshBuilder<'params, C::ScalarField, R>> {
    mesh = mesh.register_circuit_object(EndoscalarStage::into_object()?)?;

    mesh = mesh
        .register_circuit_object(PointsStage::<C::HostCurve, NUM_P_COMMITMENTS>::into_object()?)?;

    mesh = mesh.register_circuit_object(
        PointsStage::<C::HostCurve, NUM_P_COMMITMENTS>::final_into_object()?,
    )?;

    let num_steps = NumStepsLen::<NUM_P_COMMITMENTS>::len();
    for step in 0..num_steps {
        let step_circuit = EndoscalingStep::<C::HostCurve, R, NUM_P_COMMITMENTS>::new(step);
        let staged = Staged::new(step_circuit);
        mesh = mesh.register_circuit_object(staged.into_object()?)?;
    }
    Ok(mesh)
}
