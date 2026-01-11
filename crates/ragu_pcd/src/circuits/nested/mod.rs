pub mod stages;

use arithmetic::Cycle;
use ragu_circuits::{mesh::MeshBuilder, polynomials::Rank};
use ragu_core::Result;

/// Register internal nested circuits into the provided mesh.
pub(crate) fn register_all<'params, C: Cycle, R: Rank>(
    mut mesh: MeshBuilder<'params, C::ScalarField, R>,
) -> Result<MeshBuilder<'params, C::ScalarField, R>> {
    // Register a dummy circuit as placeholder for future internal scalar-field circuits.
    mesh = mesh.register_circuit(())?;
    Ok(mesh)
}
