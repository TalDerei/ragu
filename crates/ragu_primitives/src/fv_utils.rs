//! Escape hatches for the trace-extraction tooling (`qa/crates/lean_extraction`).
//!
//! This module provides constructors that bypass a gadget's invariant, so the
//! formal-verification instances can hand their symbolic input wires to the
//! real gadgets instead of re-implementing the gadgets' bodies. This module is
//! the complete list of such hatches.
//! The helpers build ordinary gadgets on a constraint-free wireless emulator,
//! then use the public gadget-mapping API to replace their dummy wires with the
//! extraction inputs; no gadget internals are exposed for this purpose.
//!
//! Gated behind the `unstable-fv` feature; not part of the stable public API.
//! `lean_extraction` is its own Cargo workspace precisely so that enabling the
//! feature cannot unify into the library builds.

use alloc::vec::{IntoIter, Vec};

use ragu_core::{
    Error, Result,
    convert::WireMap,
    drivers::{
        Driver, DriverTypes, DriverValue,
        emulator::{Emulator, Wireless},
    },
    gadgets::{Bound, Gadget},
};

use crate::{Boolean, Endoscalar};

type TemplateDriver<D> =
    Emulator<Wireless<<D as DriverTypes>::MaybeKind, <D as DriverTypes>::ImplField>>;

struct WireRemapper<D: DriverTypes> {
    wires: IntoIter<D::ImplWire>,
    actual: usize,
    consumed: usize,
}

impl<D: DriverTypes> WireRemapper<D> {
    fn new(wires: Vec<D::ImplWire>) -> Self {
        let actual = wires.len();
        Self {
            wires: wires.into_iter(),
            actual,
            consumed: 0,
        }
    }
}

impl<D: DriverTypes> WireMap<D::ImplField> for WireRemapper<D> {
    type Src = TemplateDriver<D>;
    type Dst = D;

    fn convert_wire(&mut self, _: &()) -> Result<D::ImplWire> {
        let wire = self.wires.next().ok_or(Error::VectorLengthMismatch {
            expected: self.consumed + 1,
            actual: self.actual,
        })?;
        self.consumed += 1;
        Ok(wire)
    }
}

fn remap_template<'src, 'dst, D, G>(
    template: &G,
    wires: Vec<D::ImplWire>,
) -> Result<Bound<'dst, D, G::Kind>>
where
    D: Driver<'dst>,
    G: Gadget<'src, TemplateDriver<D>>,
{
    let expected = template.num_wires()?;
    let actual = wires.len();
    if actual != expected {
        return Err(Error::VectorLengthMismatch { expected, actual });
    }

    template.map(&mut WireRemapper::<D>::new(wires))
}

/// Wraps an existing wire as a [`Boolean`] **without** constraining it.
///
/// Nothing ties `wire` to `0` or `1`; that invariant is the caller's. The
/// extraction instances use this to pass input wires to gadgets that take a
/// `&Boolean` (`Boolean::and`, `Point::conditional_negate`, …); the Lean
/// reimplementations carry the boolean-ness as an `Assumptions`.
///
/// # Errors
///
/// Returns an error if the wireless template cannot be constructed or remapped.
pub fn boolean_unchecked<'dr, D: Driver<'dr>>(
    wire: D::Wire,
    value: DriverValue<D, bool>,
) -> Result<Boolean<'dr, D>> {
    let mut dr = TemplateDriver::<D>::wireless();
    let template = Boolean::alloc(&mut dr, &mut (), value)?;
    remap_template(&template, alloc::vec![wire])
}

/// Assembles an [`Endoscalar`] from its 128 bits, least significant first,
/// **without** any check that they are booleans.
///
/// `value` is the witness the bits are supposed to encode; nothing ties the
/// two together (exactly as with [`Endoscalar::alloc`], whose `value` is also
/// unconstrained witness data). The extraction instances use this to hand
/// input-wire booleans to the real `Endoscalar::lift` / `group_scale`.
///
/// # Errors
///
/// Fails unless exactly 128 bits are given.
pub fn endoscalar_unchecked<'dr, D: Driver<'dr>>(
    bits: &[Boolean<'dr, D>],
    value: DriverValue<D, u128>,
) -> Result<Endoscalar<'dr, D>> {
    let mut dr = TemplateDriver::<D>::wireless();
    let template = Endoscalar::alloc(&mut dr, value)?;
    let wires = bits.iter().map(|bit| bit.wire().clone()).collect();
    remap_template(&template, wires)
}
