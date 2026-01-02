//! Witnessed endoscaling circuit that witnesses results instead of computing them.

use arithmetic::{CurveAffine, Uendo};
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::{GadgetKind, Kind},
    maybe::Maybe,
};
use ragu_primitives::{
    Point,
    vec::{ConstLen, FixedVec},
};

use alloc::vec::Vec;

use crate::{
    polynomials::Rank,
    staging::{StageBuilder, StagedCircuit},
};

pub use super::endoscalar::{
    EndoscalarStage, EndoscalingInstance, EndoscalingOutput, Read, SlotStage,
};

/// The key difference from [`super::endoscalar::EndoscalingWitness`] is the
/// `endoscaled_results` field, which contains the prover-computed endoscaling
/// results that the circuit will trust without verification.
pub struct WitnessedEndoscalingWitness<C: CurveAffine, const NUM_SLOTS: usize> {
    pub endoscalar: Uendo,
    pub slots: FixedVec<C, ConstLen<NUM_SLOTS>>,
    pub input: C,
    pub endoscaled_results: Vec<C>,
}

#[allow(dead_code)]
#[derive(Clone)]
pub struct WitnessedEndoscaling<C: CurveAffine, R: Rank, const NUM_SLOTS: usize> {
    pub a: Read,
    pub b: Read,
    pub c: Read,
    pub d: Read,
    pub e: Read,

    pub output: usize,

    pub _marker: core::marker::PhantomData<(C, R)>,
}

impl<C: CurveAffine, R: Rank, const NUM_SLOTS: usize> StagedCircuit<C::Base, R>
    for WitnessedEndoscaling<C, R, NUM_SLOTS>
{
    type Final = SlotStage<C, NUM_SLOTS>;
    type Instance<'source> = EndoscalingInstance<C, NUM_SLOTS>;
    type Witness<'source> = WitnessedEndoscalingWitness<C, NUM_SLOTS>;
    type Output = Kind![C::Base; EndoscalingOutput<'_, _, C>];
    type Aux<'source> = C;

    fn instance<'dr, 'source: 'dr, D: Driver<'dr, F = C::Base>>(
        &self,
        dr: &mut D,
        instance: DriverValue<D, Self::Instance<'source>>,
    ) -> Result<<Self::Output as GadgetKind<C::Base>>::Rebind<'dr, D>> {
        let input = Point::alloc(dr, instance.view().map(|instance| instance.input))?;
        let output = Point::alloc(dr, instance.view().map(|instance| instance.output))?;
        Ok(EndoscalingOutput { input, output })
    }

    fn witness<'a, 'dr, 'source: 'dr, D: Driver<'dr, F = C::Base>>(
        &self,
        dr: StageBuilder<'a, 'dr, D, R, (), Self::Final>,
        witness: DriverValue<D, Self::Witness<'source>>,
    ) -> Result<(
        <Self::Output as GadgetKind<C::Base>>::Rebind<'dr, D>,
        DriverValue<D, Self::Aux<'source>>,
    )> {
        let (endoscalar_guard, dr) = dr.add_stage::<EndoscalarStage>()?;
        let (slots_guard, dr) = dr.add_stage::<SlotStage<C, NUM_SLOTS>>()?;
        let dr = dr.finish();

        let _endoscalar = endoscalar_guard.unenforced(dr, witness.view().map(|w| w.endoscalar))?;
        let _slots = slots_guard.unenforced(dr, witness.view().map(|w| w.slots.clone()))?;

        let input = Point::alloc(dr, witness.view().map(|w| w.input))?;

        // Witness the endoscaled results directly instead of computing them.
        let mut results = Vec::with_capacity(5);
        for i in 0..5 {
            let result = Point::alloc(dr, witness.view().map(|w| w.endoscaled_results[i]))?;
            results.push(result);
        }

        let output = results[self.output].clone();
        let output_value = output.value();

        Ok((EndoscalingOutput { input, output }, output_value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CircuitExt, staging::Staged};
    use ff::Field;
    use group::prime::PrimeCurveAffine;
    use ragu_pasta::{EpAffine, Fp, Fq};
    use rand::{Rng, thread_rng};

    type R = crate::polynomials::R<13>;

    #[test]
    fn test_witnessed_endoscaling() -> Result<()> {
        const NUM_SLOTS: usize = 4;

        let endoscalar: Uendo = thread_rng().r#gen();
        let input: EpAffine = (EpAffine::generator() * Fq::random(thread_rng())).into();
        let slots: FixedVec<EpAffine, ConstLen<NUM_SLOTS>> =
            FixedVec::from_fn(|_| (EpAffine::generator() * Fq::random(thread_rng())).into());

        // We can just use stub results here. External endoscalar helper outside the circuit
        // seems unnecessary since circuit will trust whatever the prover supplies.
        let stub_results: Vec<EpAffine> = (0..5)
            .map(|_| (EpAffine::generator() * Fq::random(thread_rng())).into())
            .collect();

        let circuit = WitnessedEndoscaling::<EpAffine, R, NUM_SLOTS> {
            a: Read::Input,
            b: Read::Slot(0),
            c: Read::Slot(1),
            d: Read::Slot(2),
            e: Read::Slot(3),
            output: 4,
            _marker: core::marker::PhantomData,
        };

        let witness = WitnessedEndoscalingWitness {
            endoscalar,
            slots,
            input,
            endoscaled_results: stub_results.clone(),
        };

        let staged = Staged::new(circuit);
        let (_rx, output) = staged.rx::<R>(witness, Fp::ONE)?;

        // Output matches whatever stub we provided at index 4.
        assert_eq!(output, stub_results[4]);
        Ok(())
    }
}
