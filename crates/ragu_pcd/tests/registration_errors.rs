use ff::Field;
use ragu_circuits::polynomials::ProductionRank;
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::Bound,
};
use ragu_pasta::Pasta;
use ragu_pcd::{
    ApplicationBuilder,
    header::{Header, Leaf, Suffix},
    step::{Encoded, Index, Step},
};
use ragu_primitives::allocator::{Allocator, Standard};

// Header A with suffix 0
struct HSuffixA;
// Header B with suffix 1
struct HSuffixB;
// Different type, same suffix 0 (duplicate)
struct HSuffixAOther;

impl<F: Field> Header<F> for HSuffixA {
    const SUFFIX: Suffix = Suffix::new(0);
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

impl<F: Field> Header<F> for HSuffixB {
    const SUFFIX: Suffix = Suffix::new(1);
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

impl<F: Field> Header<F> for HSuffixAOther {
    const SUFFIX: Suffix = Suffix::new(0); // duplicate suffix
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

// Step 0 -> produces HSuffixA
struct Step0;
impl<C: ragu_arithmetic::Cycle> Step<C> for Step0 {
    const INDEX: Index = Index::new(0);
    type Witness<'source> = ();
    type Aux<'source> = ();
    type Left = ();
    type Right = ();
    type Output = HSuffixA;
    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        _: DriverValue<D, Self::Witness<'source>>,
        left: DriverValue<D, ()>,
        right: DriverValue<D, ()>,
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
        let left = Encoded::new(dr, allocator, left)?;
        let right = Encoded::new(dr, allocator, right)?;
        let output = Encoded::from_gadget(());

        Ok(((left, right, output), D::unit(), D::unit()))
    }
}

// Step 1 -> consumes A and produces B
struct Step1;
impl<C: ragu_arithmetic::Cycle> Step<C> for Step1 {
    const INDEX: Index = Index::new(1);
    type Witness<'source> = ();
    type Aux<'source> = ();
    type Left = HSuffixA;
    type Right = HSuffixA;
    type Output = HSuffixB;
    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        _: DriverValue<D, Self::Witness<'source>>,
        left: DriverValue<D, ()>,
        right: DriverValue<D, ()>,
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
        let left = Encoded::new(dr, allocator, left)?;
        let right = Encoded::new(dr, allocator, right)?;
        let output = Encoded::from_gadget(());

        Ok(((left, right, output), D::unit(), D::unit()))
    }
}

// Duplicate suffix step (index 1) producing different header with same suffix
struct Step1Dup;
impl<C: ragu_arithmetic::Cycle> Step<C> for Step1Dup {
    const INDEX: Index = Index::new(1);
    type Witness<'source> = ();
    type Aux<'source> = ();
    type Left = HSuffixA;
    type Right = HSuffixA;
    type Output = HSuffixAOther;
    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        _: DriverValue<D, Self::Witness<'source>>,
        left: DriverValue<D, ()>,
        right: DriverValue<D, ()>,
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
        let left = Encoded::new(dr, allocator, left)?;
        let right = Encoded::new(dr, allocator, right)?;
        let output = Encoded::from_gadget(());

        Ok(((left, right, output), D::unit(), D::unit()))
    }
}

#[test]
fn register_steps_success_and_finalize() {
    let pasta = Pasta::baked();
    let builder = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(Step0)
        .unwrap()
        .register(Step1)
        .unwrap();
    builder.finalize(pasta).unwrap();
}

#[test]
#[should_panic(expected = "steps must be registered in sequential order")]
fn register_steps_out_of_order_should_fail() {
    ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(Step1)
        .unwrap();
}

#[test]
#[should_panic(expected = "two different Header implementations using the same suffix")]
fn register_steps_duplicate_suffix_should_fail() {
    ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(Step0)
        .unwrap()
        .register(Step1Dup)
        .unwrap();
}

/// A seed step with no predicate producing `O` at index `I`.
struct LeafShape<O, const I: usize>(core::marker::PhantomData<O>);

impl<C, O, const I: usize> Step<C> for LeafShape<O, I>
where
    C: ragu_arithmetic::Cycle,
    O: Header<C::CircuitField, Data = (), Output = ()>,
{
    const INDEX: Index = Index::new(I);
    type Witness<'source> = ();
    type Aux<'source> = ();
    type Left = Leaf;
    type Right = Leaf;
    type Output = O;
    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        _: &mut D,
        _: DriverValue<D, Self::Witness<'source>>,
        _: DriverValue<D, ()>,
        _: DriverValue<D, ()>,
    ) -> Result<(
        (
            Encoded<'dr, D, Self::Left, HEADER_SIZE>,
            Encoded<'dr, D, Self::Right, HEADER_SIZE>,
            Encoded<'dr, D, Self::Output, HEADER_SIZE>,
        ),
        DriverValue<D, <Self::Output as Header<C::CircuitField>>::Data>,
        DriverValue<D, Self::Aux<'source>>,
    )> {
        Ok((
            (
                Encoded::from_gadget(()),
                Encoded::from_gadget(()),
                Encoded::from_gadget(()),
            ),
            D::unit(),
            D::unit(),
        ))
    }
}

#[test]
fn register_leaf_then_step_shares_index_space() {
    // Seed steps and steps share one sequential index space, and one
    // `register` method accepts both.
    ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(LeafShape::<HSuffixA, 0>(core::marker::PhantomData))
        .expect("seed step at index 0")
        .register(Step1)
        .expect("step at index 1 consuming the leaf's header")
        .finalize(Pasta::baked())
        .expect("finalize");
}

#[test]
fn register_leaf_out_of_order_should_fail() {
    assert!(
        ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
            .register(Step0)
            .unwrap()
            .register(LeafShape::<HSuffixB, 0>(core::marker::PhantomData))
            .is_err(),
        "a seed step must use the next sequential index"
    );
}

#[test]
fn register_leaf_duplicate_suffix_should_fail() {
    // Index 1 is correct here, so the failure is the suffix collision with
    // `HSuffixA`, not the index check.
    assert!(
        ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
            .register(Step0)
            .unwrap()
            .register(LeafShape::<HSuffixAOther, 1>(core::marker::PhantomData))
            .is_err(),
        "a seed step's output header must not collide with a registered one"
    );
    // Positive control: a fresh suffix at index 1 registers.
    ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(Step0)
        .unwrap()
        .register(LeafShape::<HSuffixB, 1>(core::marker::PhantomData))
        .expect("seed step with a fresh suffix at the next index registers");
}
