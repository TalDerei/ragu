//! Gadget-input helpers used only by the formal-verification extractor.
//!
//! The helpers build ordinary gadgets on a constraint-free wireless emulator,
//! then use the public gadget-mapping API to replace their dummy wires with the
//! extraction inputs. This lets instances call the real gadget implementations
//! without exposing any extraction-specific API from `ragu_primitives`.

use std::vec::{IntoIter, Vec};

use ragu_core::{
    Error, Result,
    convert::WireMap,
    drivers::{
        Driver, DriverTypes, DriverValue,
        emulator::{Emulator, Wireless},
    },
    gadgets::{Bound, Gadget},
};
use ragu_primitives::{Boolean, Endoscalar};

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

/// Wraps an existing wire as a [`Boolean`] without constraining it.
pub(crate) fn boolean_unchecked<'dr, D: Driver<'dr>>(
    wire: D::Wire,
    value: DriverValue<D, bool>,
) -> Result<Boolean<'dr, D>> {
    let mut dr = TemplateDriver::<D>::wireless();
    let template = Boolean::alloc(&mut dr, &mut (), value)?;
    remap_template(&template, vec![wire])
}

/// Assembles an [`Endoscalar`] from exactly 128 input-wire booleans.
pub(crate) fn endoscalar_unchecked<'dr, D: Driver<'dr>>(
    bits: &[Boolean<'dr, D>],
    value: DriverValue<D, u128>,
) -> Result<Endoscalar<'dr, D>> {
    let mut dr = TemplateDriver::<D>::wireless();
    let template = Endoscalar::alloc(&mut dr, value)?;
    let wires = bits.iter().map(|bit| bit.wire().clone()).collect();
    remap_template(&template, wires)
}
