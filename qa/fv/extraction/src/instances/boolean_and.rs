use ragu_pasta::Fp;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
    wire_remap::boolean_from_wire,
};

pub struct BooleanAndInstance;

impl CircuitInstance for BooleanAndInstance {
    type Field = Fp;

    /// Drives the real `Boolean::and` on two input wires wrapped as `Boolean`s
    /// (see [`boolean_from_wire`]): one mul gate plus two `enforce_equal`s,
    /// returning the gate's product wire.
    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let a_wires = dr.alloc_input_wires(1);
        let b_wires = dr.alloc_input_wires(1);
        let a = boolean_from_wire(a_wires[0].clone())?;
        let b = boolean_from_wire(b_wires[0].clone())?;

        let result = a.and(dr, &b)?;

        WireCollector::collect_from(&result)
    }
}
