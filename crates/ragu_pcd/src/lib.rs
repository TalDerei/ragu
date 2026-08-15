//! Proof-carrying data framework for Ragu.
//!
//! This crate provides the top-level API for building PCD applications:
//!
//! - [`ApplicationBuilder`] / [`Application`] — configure, build, then
//!   [`seed`](Application::seed), [`fuse`](Application::fuse),
//!   [`rerandomize`](Application::rerandomize), and
//!   [`verify`](Application::verify) proofs.
//! - [`step::Step`] — the trait that defines computation nodes (transitions).
//! - [`header::Header`] — the trait that defines succinct state representations.
//! - [`Proof`] / [`Pcd`] — the proof and proof-carrying-data structures.

#![no_std]
#![allow(clippy::type_complexity, clippy::too_many_arguments)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![doc(html_favicon_url = "https://tachyon.z.cash/assets/ragu/v1/favicon-32x32.png")]
#![doc(html_logo_url = "https://tachyon.z.cash/assets/ragu/v1/rustdoc-128x128.png")]

#[cfg(not(feature = "alloc"))]
compile_error!("`ragu_pcd` requires the `alloc` feature to be enabled.");
extern crate alloc;

#[cfg(any(feature = "std", test))]
extern crate std;

mod fuse;
#[cfg(feature = "unstable-fuzzing")]
pub mod fuzz_utils;
pub mod header;
mod internal;
mod proof;
pub mod step;
mod verify;

use alloc::collections::BTreeMap;
use core::{any::TypeId, cell::OnceCell, marker::PhantomData};

use header::Header;
pub use proof::{Pcd, Proof};
use ragu_arithmetic::{CryptoRngCore, Cycle};
use ragu_circuits::{
    polynomials::Rank,
    registry::{Registry, RegistryBuilder},
};
use ragu_core::{Error, Result};
use step::{Step, internal::adapter::Adapter};

/// Domain separation tag for Ragu PCD protocol.
// FIXME: choose a permanent domain separation tag before release.
pub(crate) const RAGU_TAG: &[u8] = b"FIXME";

/// Builder for an [`Application`] for proof-carrying data.
pub struct ApplicationBuilder<'params, C: Cycle, R: Rank, const HEADER_SIZE: usize> {
    native_registry: RegistryBuilder<'params, C::CircuitField, R>,
    nested_registry: RegistryBuilder<'params, C::ScalarField, R>,
    num_application_steps: usize,
    /// Maps each *encoded* header suffix to the [`Header`] that claimed it.
    ///
    /// Keyed on [`Suffix::get`](header::Suffix::get) rather than on the
    /// [`Suffix`](header::Suffix) itself so that an application header colliding
    /// with a reserved internal one is visible: the two are distinct `Suffix`
    /// values but encode to the same field element, and it is the encoded value
    /// that circuits compare against.
    header_map: BTreeMap<u64, TypeId>,
    _marker: PhantomData<[(); HEADER_SIZE]>,
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Default
    for ApplicationBuilder<'_, C, R, HEADER_SIZE>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'params, C: Cycle, R: Rank, const HEADER_SIZE: usize>
    ApplicationBuilder<'params, C, R, HEADER_SIZE>
{
    /// Create an empty [`ApplicationBuilder`] for proof-carrying data.
    pub fn new() -> Self {
        // Claim the reserved suffixes up front so that any application header
        // encoding to one of them is rejected by `prevent_duplicate_suffixes`.
        // This matters most for `Bootstrap`: it is the suffix that triggers the
        // base case, and an application step reaching it could skip verifying
        // its children.
        let mut header_map = BTreeMap::new();
        header_map.insert(
            <() as Header<C::CircuitField>>::SUFFIX.get(),
            TypeId::of::<()>(),
        );
        header_map.insert(
            <header::Bootstrap as Header<C::CircuitField>>::SUFFIX.get(),
            TypeId::of::<header::Bootstrap>(),
        );

        ApplicationBuilder {
            native_registry: RegistryBuilder::new(),
            nested_registry: RegistryBuilder::new(),
            num_application_steps: 0,
            header_map,
            _marker: PhantomData,
        }
    }

    /// Register a new application-defined [`Step`] in this context. The
    /// provided [`Step`]'s [`INDEX`](Step::INDEX) must be the next sequential
    /// index that has not been inserted yet.
    ///
    /// # Errors
    ///
    /// Returns an error if the step's index is not the next sequential index,
    /// or if any of the step's header suffixes conflict with an
    /// already-registered header type.
    pub fn register<S: Step<C> + 'params>(mut self, step: S) -> Result<Self> {
        S::INDEX.assert_index(self.num_application_steps)?;

        self.prevent_duplicate_suffixes::<S::Output>()?;
        self.prevent_duplicate_suffixes::<S::Left>()?;
        self.prevent_duplicate_suffixes::<S::Right>()?;

        self.native_registry =
            self.native_registry
                .register_circuit(Adapter::<C, S, R, HEADER_SIZE>::new(step))?;
        self.num_application_steps += 1;

        Ok(self)
    }

    /// Register `count` trivial circuits to simulate application steps
    /// registration.
    ///
    /// This is useful for testing internal circuit behavior with a non-zero
    /// number of application steps, without needing real [`Step`]
    /// implementations.
    #[cfg(test)]
    pub(crate) fn register_dummy_circuits(mut self, count: usize) -> Result<Self> {
        for _ in 0..count {
            self.native_registry = self.native_registry.register_circuit(())?;
            self.num_application_steps += 1;
        }
        Ok(self)
    }

    /// Perform finalization and optimization steps to produce the
    /// [`Application`].
    ///
    /// # Errors
    ///
    /// Returns an error if internal circuit registration or registry
    /// finalization fails.
    pub fn finalize(
        mut self,
        params: &'params C::Params,
    ) -> Result<Application<'params, C, R, HEADER_SIZE>> {
        // Build the native registry:
        // 1. Application circuits (already registered)
        // 2. Internal circuits and masks
        // 3. Internal steps
        let (total_circuits, log2_circuits) =
            internal::native::total_circuit_counts(self.num_application_steps);

        // First, register internal circuits and masks
        self.native_registry = internal::native::register_all::<C, R, HEADER_SIZE>(
            self.native_registry,
            params,
            log2_circuits,
        )?;

        // Then, register internal steps
        self.native_registry =
            self.native_registry
                .register_internal_step(Adapter::<C, _, R, HEADER_SIZE>::new(
                    step::internal::rerandomize::Rerandomize::<()>::new(),
                ))?;
        self.native_registry =
            self.native_registry
                .register_internal_step(Adapter::<C, _, R, HEADER_SIZE>::new(
                    step::internal::trivial::Trivial::new(),
                ))?;

        assert_eq!(
            self.native_registry.log2_circuits(),
            log2_circuits,
            "log2_circuits mismatch"
        );
        assert_eq!(
            self.native_registry.num_circuits(),
            total_circuits,
            "final circuit count mismatch"
        );

        // Register nested internal circuits (no application steps, no headers).
        self.nested_registry = internal::nested::register_all::<C, R>(self.nested_registry)?;

        Ok(Application {
            native_registry: self.native_registry.finalize()?,
            nested_registry: self.nested_registry.finalize()?,
            params,
            num_application_steps: self.num_application_steps,
            seeded_trivial: OnceCell::new(),
            _marker: PhantomData,
        })
    }

    fn prevent_duplicate_suffixes<H: Header<C::CircuitField>>(&mut self) -> Result<()> {
        match self.header_map.get(&H::SUFFIX.get()) {
            Some(ty) => {
                if *ty != TypeId::of::<H>() {
                    return Err(Error::Initialization(
                        "two different Header implementations using the same suffix".into(),
                    ));
                }
            }
            None => {
                self.header_map.insert(H::SUFFIX.get(), TypeId::of::<H>());
            }
        }

        Ok(())
    }
}

/// The recursion context that is used to create and verify proof-carrying data.
pub struct Application<'params, C: Cycle, R: Rank, const HEADER_SIZE: usize> {
    native_registry: Registry<'params, C::CircuitField, R>,
    nested_registry: Registry<'params, C::ScalarField, R>,
    params: &'params C::Params,
    num_application_steps: usize,
    /// Cached seeded trivial proof for rerandomization.
    seeded_trivial: OnceCell<Proof<C, R>>,
    _marker: PhantomData<[(); HEADER_SIZE]>,
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    /// Seed a new computation by running a step with trivial inputs.
    ///
    /// This is the entry point for creating leaf nodes in a PCD tree. The step
    /// is fused against an internally bootstrapped proof, which is a genuine
    /// `Pcd<()>`; this is an ordinary fuse whose child claims are enforced, not
    /// a base case.
    pub fn seed<'source, RNG: CryptoRngCore, S: Step<C, Left = (), Right = ()>>(
        &self,
        rng: &mut RNG,
        step: S,
        witness: S::Witness<'source>,
    ) -> Result<(Pcd<C, R, S::Output>, S::Aux<'source>)> {
        let left = self.seeded_trivial_pcd(rng)?;
        let right = self.seeded_trivial_pcd(rng)?;
        self.fuse(rng, step, witness, left, right)
    }

    /// Returns a valid `Pcd<()>` used to bootstrap the recursion.
    ///
    /// This is the one place the base case is used: two synthesized
    /// [`trivial_pcd`](Self::trivial_pcd) dummies — which cannot verify on
    /// their own — are fused through the internal
    /// [`Trivial`](step::internal::trivial::Trivial) step, the only step
    /// declaring [`Bootstrap`](header::Bootstrap) inputs. The result is a
    /// genuine proof that verifies, so [`seed`](Self::seed) and
    /// [`rerandomize`](Self::rerandomize) can consume it as an ordinary child.
    ///
    /// The proof is lazily created on first use and cached; subsequent calls
    /// return the same (non-random) proof.
    fn seeded_trivial_pcd<RNG: CryptoRngCore>(&self, rng: &mut RNG) -> Result<Pcd<C, R, ()>> {
        if self.seeded_trivial.get().is_none() {
            let (pcd, ()) = self.fuse(
                rng,
                step::internal::trivial::Trivial::new(),
                (),
                self.trivial_pcd(),
                self.trivial_pcd(),
            )?;

            // A concurrent initialization cannot happen behind `&self` here, and
            // either proof would be equally valid regardless.
            let _ = self.seeded_trivial.set(pcd.into_parts().0);
        }

        Ok(self
            .seeded_trivial
            .get()
            .expect("seeded trivial was just initialized")
            .clone()
            .carry(()))
    }

    /// Rerandomize proof-carrying data.
    ///
    /// This will internally fold the [`Pcd`] with a seeded trivial proof
    /// using an internal rerandomization step, such that the resulting proof
    /// is valid for the same [`Header`] but reveals nothing else about the
    /// original proof. As a result, [`Application::verify`] should produce the
    /// same result on the provided `pcd` as it would the output of this method.
    pub fn rerandomize<RNG: CryptoRngCore, H: Header<C::CircuitField>>(
        &self,
        pcd: Pcd<C, R, H>,
        rng: &mut RNG,
    ) -> Result<Pcd<C, R, H>> {
        // Seed a trivial proof for rerandomization.
        // TODO: this is a temporary hack that allows the base case logic to be simple
        let seeded_trivial = self.seeded_trivial_pcd(rng)?;

        // The Rerandomize step's witness() returns the left input's data as
        // output data, preserving it through rerandomization.
        self.fuse(
            rng,
            step::internal::rerandomize::Rerandomize::new(),
            (),
            pcd,
            seeded_trivial,
        )
        .map(|(pcd, ())| pcd)
    }

    /// Returns a reference to the native [`Registry`].
    pub fn native_registry(&self) -> &Registry<'_, C::CircuitField, R> {
        &self.native_registry
    }
}
