//! # `ragu_testing`
//!
//! This crate contains test fixtures and harnesses for the Ragu project. This
//! API is re-exported (as necessary) in other crates and so this crate is only
//! intended to be used internally by Ragu.

#![forbid(unsafe_code)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![doc(html_favicon_url = "https://tachyon.z.cash/assets/ragu/v1/favicon-32x32.png")]
#![doc(html_logo_url = "https://tachyon.z.cash/assets/ragu/v1/rustdoc-128x128.png")]

pub mod circuits;
pub mod patcher;
pub mod pcd;
pub mod registry;
pub mod strategies;
