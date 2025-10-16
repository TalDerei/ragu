//! Parallel iteration primitives.
//!
//! This is a zero-cost abstraction for `no_std` environments while
//! improving performance where parallelism is available.

#[cfg(feature = "multicore")]
pub use rayon::iter::{
    IndexedParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator,
};
#[cfg(feature = "multicore")]
pub use rayon::slice::ParallelSliceMut;

/// Parallel iterator over mutable chunks.
#[cfg(feature = "multicore")]
pub fn par_chunks_mut<T: Send>(
    slice: &mut [T],
    chunk_size: usize,
) -> impl ParallelIterator<Item = &mut [T]> {
    slice.par_chunks_mut(chunk_size)
}

/// Sequential fallback iterator over mutable chunks.
#[cfg(not(feature = "multicore"))]
pub fn par_chunks_mut<T>(slice: &mut [T], chunk_size: usize) -> impl Iterator<Item = &mut [T]> {
    slice.chunks_mut(chunk_size)
}

/// Parallel iteration over a slice.
#[cfg(feature = "multicore")]
pub fn par_iter<T: Sync>(slice: &[T]) -> impl IndexedParallelIterator<Item = &T> {
    slice.par_iter()
}

/// Sequential fallback iteration over a slice.
#[cfg(not(feature = "multicore"))]
pub fn par_iter<T>(slice: &[T]) -> impl Iterator<Item = &T> {
    slice.iter()
}

/// Parallel mutable iteration over a slice.
#[cfg(feature = "multicore")]
pub fn par_iter_mut<T: Send>(slice: &mut [T]) -> impl IndexedParallelIterator<Item = &mut T> {
    slice.par_iter_mut()
}

/// Sequential fallback mutable iteration over a slice.
#[cfg(not(feature = "multicore"))]
pub fn par_iter_mut<T>(slice: &mut [T]) -> impl Iterator<Item = &mut T> {
    slice.iter_mut()
}
