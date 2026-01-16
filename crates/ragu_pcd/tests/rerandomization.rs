use arithmetic::Cycle;
use ff::Field;
use ragu_circuits::polynomials::R;
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
};
use ragu_pasta::Pasta;
use ragu_pcd::{
    ApplicationBuilder,
    header::{Header, HeaderInput, HeaderOutput, Suffix},
    step::{Encoded, Index, Step, StepInput, StepOutput},
};
use rand::SeedableRng;
use rand::rngs::StdRng;

// Header A (suffix 0)
struct HeaderA;

impl<F: Field> Header<F> for HeaderA {
    const SUFFIX: Suffix = Suffix::new(0);
    type Data<'source> = ();
    type Output = ();
    fn encode<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(
        _: &mut D,
        _: HeaderInput<'source, Self, F, D>,
    ) -> Result<HeaderOutput<'dr, Self, F, D>> {
        Ok(())
    }
}

// Step0: () , ()  -> HeaderA
struct Step0;
impl<C: Cycle> Step<C> for Step0 {
    const INDEX: Index = Index::new(0);
    type Witness<'source> = ();
    type Aux<'source> = ();
    type Left = ();
    type Right = ();
    type Output = HeaderA;
    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        _: DriverValue<D, Self::Witness<'source>>,
        (left, right): StepInput<'source, Self, C, D, HEADER_SIZE>,
    ) -> Result<(
        StepOutput<'dr, Self, C, D, HEADER_SIZE>,
        DriverValue<D, Self::Aux<'source>>,
    )> {
        let left = Encoded::new(dr, left)?;
        let right = Encoded::new(dr, right)?;
        let output = Encoded::from_gadget(());
        Ok(((left, right, output), D::just(|| ())))
    }
}

struct Step1;
impl<C: Cycle> Step<C> for Step1 {
    const INDEX: Index = Index::new(1);
    type Witness<'source> = ();
    type Aux<'source> = ();
    type Left = HeaderA;
    type Right = HeaderA;
    type Output = HeaderA;
    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        _: DriverValue<D, Self::Witness<'source>>,
        (left, right): StepInput<'source, Self, C, D, HEADER_SIZE>,
    ) -> Result<(
        StepOutput<'dr, Self, C, D, HEADER_SIZE>,
        DriverValue<D, Self::Aux<'source>>,
    )> {
        let left = Encoded::new(dr, left)?;
        let right = Encoded::new(dr, right)?;
        let output = Encoded::from_gadget(());
        Ok(((left, right, output), D::just(|| ())))
    }
}

#[test]
fn rerandomization_flow() {
    let pasta = Pasta::baked();
    let app = ApplicationBuilder::<Pasta, R<13>, 4>::new()
        .register(Step0)
        .unwrap()
        .register(Step1)
        .unwrap()
        .finalize(pasta)
        .unwrap();

    let mut rng = StdRng::seed_from_u64(1234);

    let seeded = app.seed(&mut rng, Step0, ()).unwrap().0;
    let seeded = seeded.carry::<HeaderA>(());
    assert!(app.verify(&seeded, &mut rng).unwrap());

    // Rerandomize
    let seeded = app.rerandomize(seeded, &mut rng).unwrap();
    assert!(app.verify(&seeded, &mut rng).unwrap());

    let fused = app
        .fuse(&mut rng, Step1, (), seeded.clone(), seeded)
        .unwrap()
        .0;
    let fused = fused.carry::<HeaderA>(());
    assert!(app.verify(&fused, &mut rng).unwrap());

    let fused = app.rerandomize(fused, &mut rng).unwrap();
    assert!(app.verify(&fused, &mut rng).unwrap());
}
