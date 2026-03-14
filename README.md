<p align="center">
  <img width="300" height="80" src="https://tachyon.z.cash/assets/ragu/v1/github-600x160.png">
</p>

---

# `ragu` ![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/tachyon-zcash/ragu)

**Ragu** is a Rust-language [proof-carrying data (PCD)](https://ic-people.epfl.ch/~achiesa/docs/CT10.pdf) framework that implements a modified version of the ECDLP-based recursive SNARK construction from [Halo [BGH19]](https://eprint.iacr.org/2019/1021). Ragu does not require a trusted setup. Developed for [Project Tachyon](https://tachyon.z.cash/) and compatible with the [Pasta curves](https://electriccoin.co/blog/the-pasta-curves-for-halo-2-and-beyond/) employed in [Zcash](https://z.cash/), Ragu targets performance and feature support that is competitive with other ECC-based [accumulation](https://eprint.iacr.org/2020/499)/[folding](https://eprint.iacr.org/2021/370) schemes without complicated circuit arithmetizations.

> ⚠️ **Ragu is under heavy development and has not undergone auditing.** Do not use this software in production.

## Resources

* [The Ragu Book](https://tachyon.z.cash/ragu/) provides high-level documentation about Ragu, how it can be used, how it is designed, and how to contribute. The source code for the book lives in this repository in the [`book`](https://github.com/tachyon-zcash/ragu/tree/main/book) subdirectory.
* [Crate documentation](https://docs.rs/ragu) is available for official Ragu crate releases.
* Unofficial (internal) library documentation is [continually rendered](https://tachyon.z.cash/ragu/internal/ragu/) from the `main` branch. This is primarily for developers of Ragu.

## Minimum Supported Rust Version

Requires Rust **1.90** or higher. The minimum supported Rust version (MSRV) may be changed in the future, but it will be done with a minor version bump.

## Controlling Parallelism

`ragu` uses [`maybe-rayon`](https://crates.io/crates/maybe-rayon) for parallel computation. Parallelism is enabled via the `multicore` feature flag, which is **on by default**. The number of threads can be controlled with the `RAYON_NUM_THREADS` environment variable.

To disable parallelism (e.g. for `no_std` or single-threaded targets):

```
cargo build --no-default-features
```

This will cause `ragu` to perform all computation on a single thread, which will significantly degrade performance.

## License

This library is distributed under the terms of both the MIT license and the Apache License (Version 2.0). See [LICENSE-APACHE](./LICENSE-APACHE), [LICENSE-MIT](./LICENSE-MIT) and [COPYRIGHT](./COPYRIGHT).
