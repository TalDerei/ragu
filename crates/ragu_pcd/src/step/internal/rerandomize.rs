//! Rerandomization step for PCDs.
//!
//! This is a simple step: it takes a header and folds the proof carrying it
//! with itself, producing the same header. To keep the circuit identical no
//! matter what the header is, we use a _uniform_ encoding — which makes every
//! header slot, including the suffix, a witness wire rather than a constant.
//!
//! That witnessed suffix is the one place outside the bootstrap step where a
//! prover could try to present the [`Dummy`] suffix and take the base case.
//! Two things stop it. All three header slots — both inputs and the output —
//! are the *same* wires, so the output header is pinned equal to the input
//! (no relabelling on the way through) and both children must carry the same
//! encoded header; `test_rerandomize_consistency` pins that structurally. And
//! [`Encoded::new_uniform`] constrains the suffix wire away from `Dummy`,
//! making the base case unsatisfiable here.
//!
//! The circuit binds the children to the same *header*, not the same *proof*:
//! an honest prover passes one proof twice, and any valid proof of that header
//! on the right is equally harmless, since its claims are folded and enforced
//! but it contributes nothing to the output. Folding a proof with itself is
//! what lets rerandomization avoid consuming the bootstrap proof, leaving that
//! to seed steps alone.
//!
//! [`Dummy`]: crate::header::Dummy
//! [`Encoded::new_uniform`]: crate::step::Encoded::new_uniform

use core::marker::PhantomData;

use ragu_arithmetic::Cycle;
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    maybe::Maybe,
};
use ragu_primitives::allocator::Standard;

use super::super::{Encoded, Index, Step};
use crate::Header;
pub(crate) use crate::step::InternalStepIndex::Rerandomize as INTERNAL_ID;

pub(crate) struct Rerandomize<H> {
    _marker: PhantomData<H>,
}

impl<H> Rerandomize<H> {
    pub fn new() -> Self {
        Rerandomize {
            _marker: PhantomData,
        }
    }
}

impl<C: Cycle, H: Header<C::CircuitField>> Step<C> for Rerandomize<H> {
    const INDEX: Index = Index::internal(INTERNAL_ID);

    type Witness<'source> = ();
    type Aux<'source> = ();

    type Left = H;
    type Right = H;
    type Output = H;

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        _: DriverValue<D, Self::Witness<'source>>,
        left: DriverValue<D, H::Data>,
        _right: DriverValue<D, H::Data>,
    ) -> Result<(
        (
            Encoded<'dr, D, Self::Left, HEADER_SIZE>,
            Encoded<'dr, D, Self::Right, HEADER_SIZE>,
            Encoded<'dr, D, Self::Output, HEADER_SIZE>,
        ),
        DriverValue<D, <Self::Output as Header<C::CircuitField>>::Data>,
        DriverValue<D, Self::Aux<'source>>,
    )> {
        let allocator = &mut Standard::new();

        // Uniform encoding keeps this circuit identical across header types and
        // constrains the witnessed suffix away from `Dummy` (see
        // `Encoded::new_uniform`). One wire set serves as left input, right
        // input, and output header (see the module docs), so `right`
        // contributes nothing here beyond its type.
        let encoded = Encoded::new_uniform(dr, allocator, left.clone())?;

        // TODO(ebfull): It's possible that the witness for this step needs to
        // be populated with some random data, for actual re-randomization
        // (zero-knowledge), though it's not certain at this stage in
        // development. Note that random wires here would only randomize this
        // step's own application polynomial, which is already blinded; the
        // folded accumulator of the resulting proof is a deterministic function
        // of the input proof and the public challenges, so hiding it would need
        // a fold-level randomizer claim rather than extra witness here.

        // Return left's data as the output data - this preserves it!
        Ok(((encoded.clone(), encoded.clone(), encoded), left, D::unit()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rerandomize_consistency() {
        use ragu_circuits::polynomials;
        use ragu_core::{
            Result,
            drivers::{Driver, DriverValue},
            gadgets::{Bound, Kind},
            maybe::Maybe,
        };
        use ragu_pasta::{Fp, Pasta};
        use ragu_primitives::{Element, allocator::Allocator};
        use ragu_testing::registry::TestRegistryBuilder;

        use crate::header::{Header, Suffix};

        const HEADER_SIZE: usize = 4;
        type R = polynomials::TestRank;

        struct Single;
        impl Header<Fp> for Single {
            const SUFFIX: Suffix = Suffix::new(0);
            type Data = Fp;
            type Output = Kind![Fp; Element<'_, _>];
            fn encode<'dr, D: Driver<'dr, F = Fp>, A: Allocator<'dr, D>>(
                dr: &mut D,
                allocator: &mut A,
                witness: DriverValue<D, Self::Data>,
            ) -> Result<Bound<'dr, D, Self::Output>> {
                Element::alloc(dr, allocator, witness)
            }
        }

        struct Pair;
        impl Header<Fp> for Pair {
            const SUFFIX: Suffix = Suffix::new(1);
            type Data = (Fp, Fp);
            type Output = Kind![Fp; (Element<'_, _>, Element<'_, _>)];
            fn encode<'dr, D: Driver<'dr, F = Fp>, A: Allocator<'dr, D>>(
                dr: &mut D,
                allocator: &mut A,
                witness: DriverValue<D, Self::Data>,
            ) -> Result<Bound<'dr, D, Self::Output>> {
                let (a, b) = witness.cast();
                let a = Element::alloc(dr, allocator, a)?;
                let b = Element::alloc(dr, allocator, b)?;

                Ok((a, b))
            }
        }

        let circuit_single =
            super::super::adapter::Adapter::<Pasta, Rerandomize<Single>, R, HEADER_SIZE>::new(
                Rerandomize::new(),
            );
        let circuit_pair =
            super::super::adapter::Adapter::<Pasta, Rerandomize<Pair>, R, HEADER_SIZE>::new(
                Rerandomize::new(),
            );

        // `Rerandomize<()>` is the instantiation `finalize` actually registers.
        let circuit_unit =
            super::super::adapter::Adapter::<Pasta, Rerandomize<()>, R, HEADER_SIZE>::new(
                Rerandomize::new(),
            );

        // A frozen twin of `Rerandomize`, written from primitives: exactly one
        // uniform-encoded header, whose wires serve as left input, right
        // input, and output. `Rerandomize` must stay wiring-identical to this,
        // which pins the load-bearing fact that its three header slots are one
        // wire set — a separately encoded slot (fresh wires) would let a prover
        // relabel the header on the way through, and no end-to-end test can
        // express that witness while the wires are shared.
        struct OneWireSet;
        impl Step<Pasta> for OneWireSet {
            const INDEX: Index = Index::internal(INTERNAL_ID);
            type Witness<'source> = ();
            type Aux<'source> = ();
            type Left = ();
            type Right = ();
            type Output = ();
            fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = Fp>, const HS: usize>(
                &self,
                dr: &mut D,
                _: DriverValue<D, ()>,
                left: DriverValue<D, ()>,
                _right: DriverValue<D, ()>,
            ) -> Result<(
                (
                    Encoded<'dr, D, (), HS>,
                    Encoded<'dr, D, (), HS>,
                    Encoded<'dr, D, (), HS>,
                ),
                DriverValue<D, ()>,
                DriverValue<D, ()>,
            )> {
                let allocator = &mut ragu_primitives::allocator::Standard::new();
                let encoded = Encoded::<'dr, D, (), HS>::new_uniform(dr, allocator, left.clone())?;
                Ok(((encoded.clone(), encoded.clone(), encoded), left, D::unit()))
            }
        }
        let circuit_twin =
            super::super::adapter::Adapter::<Pasta, OneWireSet, R, HEADER_SIZE>::new(OneWireSet);

        let mut builder: TestRegistryBuilder<'_, _, R> = TestRegistryBuilder::new();
        let single_h = builder.register_circuit(circuit_single).unwrap();
        let pair_h = builder.register_circuit(circuit_pair).unwrap();
        let unit_h = builder.register_circuit(circuit_unit).unwrap();
        let twin_h = builder.register_circuit(circuit_twin).unwrap();
        let registry = builder.finalize().unwrap();

        let x = Fp::from(5u64);
        let y = Fp::from(17u64);

        assert_eq!(registry.xy(single_h, x, y), registry.xy(pair_h, x, y));
        assert_eq!(registry.xy(single_h, x, y), registry.xy(unit_h, x, y));
        assert_eq!(
            registry.xy(unit_h, x, y),
            registry.xy(twin_h, x, y),
            "Rerandomize must use one uniform wire set for its left, right, and output header slots"
        );
    }
}
