//! # Polyvalue
//! Single concrete type for representing values of different types
//!
//! ## Usage
//! ```rust
//! use polyvalue::{Value, Int, Float, Fixed, Currency, Str, Array, Object};
//!
//! fn main() {
//!     let v = Value::from(1);
//!     assert_eq!(v, Value::Int(Int::new(1)));
//!
//!     let v = Value::from(1.0).arithmetic_op(&Value::from(2.0), ArithmeticOperation::Add).unwrap();
//!     assert_eq!(v, Value::Float(Float::new(3.0)));
//! }
//! ```
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
