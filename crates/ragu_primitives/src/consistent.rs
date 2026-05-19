//! The [`Consistent`] trait — implemented for gadgets that are capable of
//! emitting constraints to re-express all of their invariants.

use alloc::boxed::Box;

use ragu_core::{Result, drivers::Driver, gadgets::Gadget};

/// Implemented for gadgets that are capable of emitting constraints to
/// re-express all of their invariants on the wires inside `self`.
///
/// Not every gadget can implement this.
///
/// [`Point`] re-enforces its curve equation; [`Boolean`] re-enforces 0/1;
/// [`Element`] is a no-op. Composite gadgets derived with the
/// [`Consistent`](derive@Consistent) macro delegate to their
/// `#[ragu(gadget)]` fields.
///
/// [`Point`]: crate::Point
/// [`Boolean`]: crate::Boolean
/// [`Element`]: crate::Element
pub trait Consistent<'dr, D: Driver<'dr>>: Gadget<'dr, D> {
    /// Emit constraints that re-express `Self`'s invariants on the wires
    /// inside `self`, against the driver `dr`.
    fn enforce_consistent(&self, dr: &mut D) -> Result<()>;
}

/// Derives [`Consistent`] by calling `enforce_consistent` on `#[ragu(gadget)]` fields.
pub use ragu_macros::Consistent;

impl<'dr, D: Driver<'dr>> Consistent<'dr, D> for () {
    fn enforce_consistent(&self, _: &mut D) -> Result<()> {
        Ok(())
    }
}

impl<'dr, D: Driver<'dr>, G: Consistent<'dr, D>, const N: usize> Consistent<'dr, D> for [G; N] {
    fn enforce_consistent(&self, dr: &mut D) -> Result<()> {
        for item in self.iter() {
            item.enforce_consistent(dr)?;
        }
        Ok(())
    }
}

impl<'dr, D: Driver<'dr>, G1: Consistent<'dr, D>, G2: Consistent<'dr, D>> Consistent<'dr, D>
    for (G1, G2)
{
    fn enforce_consistent(&self, dr: &mut D) -> Result<()> {
        self.0.enforce_consistent(dr)?;
        self.1.enforce_consistent(dr)?;
        Ok(())
    }
}

impl<'dr, D: Driver<'dr>, G: Consistent<'dr, D>> Consistent<'dr, D> for Box<G> {
    fn enforce_consistent(&self, dr: &mut D) -> Result<()> {
        (**self).enforce_consistent(dr)
    }
}
