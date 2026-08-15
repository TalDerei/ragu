//! Headers are succinct representations of data used to represent the current
//! state of a computation.

use core::any::Any;

use ragu_arithmetic::ff::Field;
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::Bound,
};
use ragu_primitives::{allocator::Allocator, io::Write};

/// The number of suffixes used internally by Ragu.
///
/// * `0` is reserved for all circuits that have a fixed ID, used internally for
///   recursion. This is not used by actual [`Header`] implementations.
/// * `1` is reserved for the trivial header.
/// * `2` is reserved for the [`Bootstrap`] header, the input type of the
///   internal [`Trivial`] step. It is the only suffix that triggers the base
///   case, and no application [`Step`] can declare it as an input, which is
///   what confines the base case to genuine bootstrapping.
///
/// [`Trivial`]: crate::step::internal::trivial::Trivial
/// [`Step`]: crate::step::Step
const NUM_INTERNAL_SUFFIXES: u8 = 3;

/// Internal representation of a [`Suffix`] distinguishing internal vs.
/// application suffixes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
enum HeaderSuffix {
    Internal(usize),
    Application(usize),
}

/// The unique suffix for a [`Header`].
///
/// All steps register an `Output` header that represents their computational
/// state. In order to distinguish headers (regardless of the step that produced
/// them) a suffix is appended to each header.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub struct Suffix {
    suffix: HeaderSuffix,
}

impl Suffix {
    /// Creates a new application-defined [`Header`] suffix.
    ///
    /// ## Panics
    ///
    /// Panics if `value` is large enough that offsetting it past the internal
    /// suffixes would overflow. Without this bound an application suffix could
    /// wrap onto a reserved internal one — in particular onto the bootstrap
    /// suffix, which would let an application [`Step`] present the suffix that
    /// triggers the base case. Overflow checks are disabled in release builds,
    /// so this bound is enforced explicitly rather than relying on the addition
    /// to trap.
    ///
    /// [`Step`]: crate::step::Step
    pub const fn new(value: usize) -> Self {
        assert!(
            value <= usize::MAX - NUM_INTERNAL_SUFFIXES as usize,
            "application header suffix would overflow onto a reserved internal suffix"
        );

        Suffix {
            suffix: HeaderSuffix::Application(value),
        }
    }

    /// Obtain this suffix's `u64` value based on whether this represents an
    /// internal or application [`Header`] suffix.
    pub(crate) fn get(&self) -> u64 {
        match self.suffix {
            HeaderSuffix::Internal(i) => i as u64,
            HeaderSuffix::Application(i) => (i + NUM_INTERNAL_SUFFIXES as usize) as u64,
        }
    }

    /// Creates a new internal-defined [`Header`] suffix. Only called internally
    /// by Ragu.
    pub(crate) const fn internal(value: usize) -> Self {
        assert!(
            value < NUM_INTERNAL_SUFFIXES as usize,
            "invalid internal header suffix index"
        );

        Suffix {
            suffix: HeaderSuffix::Internal(value),
        }
    }

    /// The reserved suffix of the [`Bootstrap`] header. Only called internally
    /// by Ragu.
    pub(crate) const fn bootstrap() -> Self {
        Suffix::internal(2)
    }
}

#[test]
fn test_suffix_map() {
    assert_eq!(Suffix::internal(0).get(), 0);
    assert_eq!(Suffix::internal(1).get(), 1);
    assert_eq!(Suffix::bootstrap().get(), 2);
    assert_eq!(Suffix::new(0).get(), 3);
    assert_eq!(Suffix::new(1).get(), 4);
}

#[test]
#[should_panic(expected = "overflow onto a reserved internal suffix")]
fn application_suffix_cannot_wrap_onto_a_reserved_suffix() {
    // Offsetting past the internal suffixes must not wrap an application suffix
    // onto a reserved one. `usize::MAX` would otherwise encode to
    // `Suffix::bootstrap()`, letting an application `Step` declare the input
    // type that triggers the base case. Overflow checks are off in release
    // builds, so the bound is enforced explicitly.
    let _ = Suffix::new(usize::MAX);
}

/// Headers are succinct representations of data, essentially used as public
/// inputs to recursive proofs in order to represent the current state of the
/// computation.
///
/// See the [Writing Circuits](https://tachyon.z.cash/ragu/guide/writing_circuits.html)
/// guide for usage patterns and examples.
pub trait Header<F: Field>: Send + Sync + Any {
    /// Each header should use a unique suffix to distinguish itself from other
    /// headers.
    const SUFFIX: Suffix;

    /// The data needed to encode a header.
    type Data: Send + Clone;

    /// The output gadget that encodes the data for this header.
    type Output: Write<F>;

    /// Encode some data into a gadget representing this header.
    ///
    /// Implementations should pass `allocator` through to all allocation
    /// calls rather than substituting a different allocator.
    fn encode<'dr, D: Driver<'dr, F = F>, A: Allocator<'dr, D>>(
        dr: &mut D,
        allocator: &mut A,
        witness: DriverValue<D, Self::Data>,
    ) -> Result<Bound<'dr, D, Self::Output>>;
}

/// Trivial header that encodes no data.
impl<F: Field> Header<F> for () {
    const SUFFIX: Suffix = Suffix::internal(1);

    type Data = ();
    type Output = ();

    fn encode<'dr, D: Driver<'dr, F = F>, A: Allocator<'dr, D>>(
        _: &mut D,
        _: &mut A,
        _: DriverValue<D, Self::Data>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Ok(())
    }
}

/// The reserved header marking the inputs consumed when bootstrapping the
/// recursion.
///
/// This header encodes no data; it exists only for its
/// [suffix](Suffix::bootstrap). The internal
/// [`Trivial`](crate::step::internal::trivial::Trivial) step is the only step
/// that declares it as an input type, so it is the only step whose fuse is
/// treated as the base case.
///
/// Base-case detection rests on a property of the current step rather than on
/// anything the child proofs carry: the suffix traces back to a constant that
/// [`padded::for_header`](crate::step::internal::padded::for_header) bakes into
/// the step's application circuit. See
/// [`is_bootstrap_input`](crate::internal::native::stages::preamble::ProofInputs::is_bootstrap_input)
/// for how that binding is established.
///
/// This rests in turn on no application header being able to encode to this
/// suffix, which [`Suffix::new`] and
/// [`ApplicationBuilder`](crate::ApplicationBuilder) enforce.
pub(crate) struct Bootstrap;

impl<F: Field> Header<F> for Bootstrap {
    const SUFFIX: Suffix = Suffix::bootstrap();

    type Data = ();
    type Output = ();

    fn encode<'dr, D: Driver<'dr, F = F>, A: Allocator<'dr, D>>(
        _: &mut D,
        _: &mut A,
        _: DriverValue<D, Self::Data>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        Ok(())
    }
}
