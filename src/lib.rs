//! # Polyvalue
//! Single concrete type for representing values of different types
//!
//! This crate was built for use in a parser, where the type of a value is not known until runtime.
//! Please open an issue if you have any suggestions for improvement.
//!
#![doc(html_root_url = "https://docs.rs/polyvalue/0.1.0")]
#![warn(missing_docs)]

#[macro_use]
mod macros;

mod error;
pub use error::Error;

mod value;
pub use value::*;

pub mod operations;
pub mod types;

// We will export the fpdec crate as well, so that users can use it directly
pub use fpdec;
