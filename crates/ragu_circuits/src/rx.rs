//! Assembly of the $r(X)$ trace polynomial.
//!
//! The [`eval`] function in this module processes some witness data for a
//! particular [`Circuit`] and assembles the corresponding $r(X)$ trace polynomial.

use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::{
    Error, Result,
    drivers::{Driver, DriverTypes, emulator::Emulator},
    gadgets::{Bound, GadgetKind},
    maybe::{Always, Maybe, MaybeKind},
    routines::Routine,
};
use ragu_primitives::GadgetExt;

use alloc::vec::Vec;

use super::{Circuit, DriverScope, Rank, registry, structured};

/// Opaque trace produced by [`CircuitExt::rx`](crate::CircuitExt::rx).
///
/// Callers must go through
/// [`Registry::assemble`](crate::registry::Registry::assemble) (or
/// [`assemble_trivial`](Self::assemble_trivial) in tests) to obtain the final
/// polynomial.
pub struct Trace<F: Field> {
    pub(crate) a: Vec<F>,
    pub(crate) b: Vec<F>,
    pub(crate) c: Vec<F>,
}

impl<F: Field> Trace<F> {
    /// Assembles the trace into a polynomial, embedding the given `key`.
    pub(crate) fn assemble_with_key<R: Rank>(
        &self,
        key: &registry::Key<F>,
    ) -> Result<structured::Polynomial<F, R>> {
        if self.a.len() > R::n() || self.b.len() > R::n() || self.c.len() > R::n() {
            return Err(Error::MultiplicationBoundExceeded(R::n()));
        }
        let mut poly = structured::Polynomial::<F, R>::new();
        {
            let view = poly.forward();
            for val in &self.a {
                view.a.push(*val);
            }
            for val in &self.b {
                view.b.push(*val);
            }
            for val in &self.c {
                view.c.push(*val);
            }
            view.a[0] = key.value();
            view.b[0] = key.inverse();
            view.c[0] = F::ONE;
        }
        Ok(poly)
    }

    /// Assembles the trace into a polynomial using a trivial floor plan.
    ///
    /// For use in tests and benchmarks that don't have a registry.
    pub fn assemble_trivial<R: Rank>(self) -> Result<structured::Polynomial<F, R>> {
        self.assemble_with_key(&registry::Key::default())
    }
}

struct Evaluator<'a, F: Field> {
    trace: &'a mut Trace<F>,
    available_b: Option<usize>,
}

impl<F: Field> DriverScope<Option<usize>> for Evaluator<'_, F> {
    fn scope(&mut self) -> &mut Option<usize> {
        &mut self.available_b
    }
}

impl<F: Field> DriverTypes for Evaluator<'_, F> {
    type ImplField = F;
    type ImplWire = ();
    type MaybeKind = Always<()>;
    type LCadd = ();
    type LCenforce = ();
}

impl<'a, F: Field> Driver<'a> for Evaluator<'a, F> {
    type F = F;
    type Wire = ();
    const ONE: Self::Wire = ();

    fn alloc(&mut self, value: impl Fn() -> Result<Coeff<Self::F>>) -> Result<Self::Wire> {
        // Packs two allocations into one multiplication gate when possible, enabling consecutive
        // allocations to share gates.
        if let Some(index) = self.available_b.take() {
            let a = self.trace.a[index];
            let b = value()?;
            self.trace.b[index] = b.value();
            self.trace.c[index] = a * b.value();
            Ok(())
        } else {
            let index = self.trace.a.len();
            self.mul(|| Ok((value()?, Coeff::Zero, Coeff::Zero)))?;
            self.available_b = Some(index);
            Ok(())
        }
    }

    fn mul(
        &mut self,
        values: impl Fn() -> Result<(Coeff<Self::F>, Coeff<Self::F>, Coeff<Self::F>)>,
    ) -> Result<((), (), ())> {
        let (a, b, c) = values()?;
        self.trace.a.push(a.value());
        self.trace.b.push(b.value());
        self.trace.c.push(c.value());

        Ok(((), (), ()))
    }

    fn add(&mut self, _: impl Fn(Self::LCadd) -> Self::LCadd) -> Self::Wire {}

    fn enforce_zero(&mut self, _: impl Fn(Self::LCenforce) -> Self::LCenforce) -> Result<()> {
        Ok(())
    }

    fn routine<Ro: Routine<Self::F> + 'a>(
        &mut self,
        routine: Ro,
        input: Bound<'a, Self, Ro::Input>,
    ) -> Result<Bound<'a, Self, Ro::Output>> {
        self.with_scope(None, |this| {
            let mut dummy = Emulator::wireless();
            let dummy_input = Ro::Input::map_gadget(&input, &mut dummy)?;
            let aux = routine.predict(&mut dummy, &dummy_input)?.into_aux();
            routine.execute(this, input, aux)
        })
    }
}

pub fn eval<'witness, F: Field, C: Circuit<F>>(
    circuit: &C,
    witness: C::Witness<'witness>,
) -> Result<(Trace<F>, C::Aux<'witness>)> {
    let mut trace = Trace {
        a: Vec::new(),
        b: Vec::new(),
        c: Vec::new(),
    };
    let aux = {
        let mut dr = Evaluator {
            trace: &mut trace,
            available_b: None,
        };
        dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
        let (io, aux) = circuit.witness(&mut dr, Always::maybe_just(|| witness))?;
        io.write(&mut dr, &mut ())?;

        aux.take()
    };
    Ok((trace, aux))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomials::TestRank;
    use crate::tests::SquareCircuit;
    use ragu_pasta::Fp;

    #[test]
    fn test_rx() {
        let circuit = SquareCircuit { times: 10 };
        let witness: Fp = Fp::from(3);
        let (trace, _aux) = eval::<Fp, _>(&circuit, witness).unwrap();
        let rx = trace.assemble_trivial::<TestRank>().unwrap();
        let mut coeffs = rx.iter_coeffs().collect::<Vec<_>>();
        let size_of_vec = coeffs.len() / 4;
        let c = coeffs.drain(..size_of_vec).collect::<Vec<_>>();
        let b = coeffs.drain(..size_of_vec).rev().collect::<Vec<_>>();
        let a = coeffs.drain(..size_of_vec).collect::<Vec<_>>();
        let d = coeffs.drain(..size_of_vec).rev().collect::<Vec<_>>();
        for i in 0..size_of_vec {
            assert_eq!(a[i] * b[i], c[i]);
            assert_eq!(d[i], Fp::ZERO);
        }
    }
}
