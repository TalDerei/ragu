mod driver;
mod expr;
mod instance;
mod instances;
mod linexp;

use instance::CircuitInstance;

use crate::instances::{
    point_add::PointAddInstance, point_alloc::PointAllocInstance,
    point_double::PointDoubleInstance, point_neg::PointNegInstance,
};

fn main() {
    println!("-- Point allocation instance:");
    PointAllocInstance::export();
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
