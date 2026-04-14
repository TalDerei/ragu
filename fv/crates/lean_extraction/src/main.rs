mod driver;
mod expr;
mod instance;
mod instances;
mod linexp;

use instance::CircuitInstance;

use crate::instances::{
    point_add::PointAddInstance,
    point_alloc::{PointAllocInstanceFp, PointAllocInstanceFq},
    point_double::PointDoubleInstance,
    point_neg::PointNegInstance,
};

fn main() {
    println!("-- Point allocation instance (Fp):");
    PointAllocInstanceFp::export();
    println!("-----------------");

    println!("-- Point allocation instance (Fq):");
    PointAllocInstanceFq::export();
    println!("-----------------");

    println!("-- Point negation instance:");
    PointNegInstance::export();
    println!("-----------------");

    println!("-- Point doubling instance:");
    PointDoubleInstance::export();
    println!("-----------------");

    println!("-- Point add instance:");
    PointAddInstance::export();
    println!("-----------------");
}
