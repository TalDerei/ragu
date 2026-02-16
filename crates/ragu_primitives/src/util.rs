//! This is an internal module used to store helper utilities that are not part
//! of the public API (yet).

use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::perhaps::{Perhaps, Wrap};

use core::borrow::Borrow;

/// Extension trait for `Perhaps` that provides helper methods kept internal to
/// this crate.
pub(crate) trait InternalPerhaps<T: Send>: Perhaps<T> {
    /// Convert a `bool` into a `Field` element.
    fn fe<U, F: Field>(&self) -> Wrap<<Self as Perhaps<U>>::Kind, F>
    where
        Self: Perhaps<U>,
        U: Borrow<bool> + Send + Sync,
    {
        Perhaps::<U>::view(self).map(|b| if *b.borrow() { F::ONE } else { F::ZERO })
    }

    /// Convert a `bool` into a `Coeff`.
    fn coeff<U, F: Field>(&self) -> Wrap<<Self as Perhaps<U>>::Kind, Coeff<F>>
    where
        Self: Perhaps<U>,
        U: Borrow<bool> + Send + Sync,
    {
        Perhaps::<U>::view(self).map(|b| if *b.borrow() { Coeff::One } else { Coeff::Zero })
    }

    /// Convert an arbitrary `Field` element into a `Coeff`.
    fn arbitrary<U, F: Field>(&self) -> Wrap<<Self as Perhaps<U>>::Kind, Coeff<F>>
    where
        Self: Perhaps<U>,
        U: Borrow<F> + Send + Sync,
    {
        Perhaps::<U>::view(self).map(|f| Coeff::Arbitrary(*f.borrow()))
    }

    /// Negate a `bool`.
    fn not<U>(&self) -> Wrap<<Self as Perhaps<U>>::Kind, bool>
    where
        Self: Perhaps<U>,
        U: Borrow<bool> + Send + Sync,
    {
        Perhaps::<U>::view(self).map(|b| !*b.borrow())
    }
}

impl<T: Send, M: Perhaps<T>> InternalPerhaps<T> for M {}
