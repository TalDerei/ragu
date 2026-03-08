# Requirements

* The minimum supported [Rust](https://rust-lang.org/) version is currently
  **1.90.0**.
* Ragu requires minimal dependencies and currently strives to avoid using
  dependencies that are not already used in
  [Zebra](https://github.com/ZcashFoundation/zebra).

## Standard Library Usage

Ragu's core crates (`ragu_arithmetic`, `ragu_core`, `ragu_primitives`,
`ragu_pasta`, `ragu_pcd`) are all `#![no_std]` and do not depend on the Rust
standard library. They do, however, require the [`alloc`] crate for
heap-allocated types such as `Vec` and `Box`. In practice this means Ragu can
target environments that provide a global allocator but lack a full `std`
runtime, such as WebAssembly or embedded platforms.

A small number of crates fall outside this constraint:

* `ragu_macros` is a procedural-macro crate, which always runs on the host at
  compile time and therefore requires `std`.
* `ragu_testing` is a test-only utility crate and does not need to be
  `no_std`-compatible.
* `ragu_pcd` conditionally enables `std` during tests via
  `#![cfg_attr(not(test), no_std)]`, while remaining `no_std` in release
  builds.

Optional features may also introduce `std` usage. For example,
`ragu_arithmetic`'s `multicore` feature gates multi-threaded parallelism
behind `std`.

## The Primitives Standard Library

The [`ragu_primitives`] crate serves as a **standard library for circuit
developers**. While `ragu_core` defines the fundamental `Driver` abstraction
and related traits, `ragu_primitives` builds on that foundation to provide
the concrete gadgets and utilities that most circuit code depends on:

* **Core gadgets** — [`Element`], [`Boolean`], and [`Point`] provide
  in-circuit representations of field elements, boolean values, and elliptic
  curve points respectively.
* **Cryptographic primitives** — the [Poseidon] sponge hash and
  [`Endoscalar`] challenge gadget for efficient curve arithmetic using
  endomorphisms.
* **Serialization** — the [`Write`][write-trait] trait and [`Buffer`]
  interface standardize how gadgets are serialized to field elements.
* **Containers** — [`FixedVec`] provides a length-typed vector that
  satisfies the `Gadget` trait, ensuring circuit structure is determined by
  types rather than runtime values.
* **Development tooling** — the [`Simulator`] driver executes circuit code
  in-memory for testing and debugging without generating proofs.
* **Gadget utilities** — [demotion and promotion][promotion] for stripping
  and recovering witness data, [consistency enforcement][consistent] for
  re-checking gadget constraints, and thread-safe wrappers via [`Sendable`].

Most Ragu applications will depend on `ragu_primitives` directly, and the
user guide covers its gadgets extensively in the chapters that follow.

[`alloc`]: https://doc.rust-lang.org/alloc/
[`ragu_primitives`]: https://docs.rs/ragu_primitives
[`Element`]: ragu_primitives::Element
[`Boolean`]: ragu_primitives::Boolean
[`Point`]: ragu_primitives::point::Point
[Poseidon]: ragu_primitives::poseidon::Sponge
[`Endoscalar`]: ragu_primitives::endoscalar::Endoscalar
[write-trait]: ragu_primitives::io::Write
[`Buffer`]: ragu_primitives::io::Buffer
[`FixedVec`]: ragu_primitives::vec::FixedVec
[`Simulator`]: ragu_primitives::Simulator
[promotion]: ragu_primitives::promotion
[consistent]: ragu_primitives::consistent::Consistent
[`Sendable`]: ragu_primitives::sendable::Sendable
