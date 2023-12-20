//! # Polyvalue
//! Single concrete type for representing values of different types
//!
//! This crate was built for use in a parser, where the type of a value is not known until runtime.
//! Please open an issue if you have any suggestions for improvement.
//!
//! It provides a new type, [`Value`](crate::Value), which is an enum around a set of types implementing
//! a common trait, [`ValueTrait`](crate::ValueTrait).
//!
//! All types will also implement all of the following:
//! Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default
//!
//! The following types are provided:
//! - [`Bool`](crate::Bool) : Wraps a `bool`
//! - [`Int`](crate::Int) : Wraps an `i64`
//! - [`Float`](crate::Float) : Wraps an `f64`
//! - [`Fixed`](crate::Fixed) : Wraps an `fpdec::Decimal`, a fixed-point decimal type
//! - [`Currency`](crate::Currency) : Wraps a `Fixed` and adds a currency symbol
//! - [`Str`](crate::Str) : Wraps a `String`
//! - [`Array`](crate::Array) : Wraps a `Vec<Value>`, providing an ordered set
//! - [`Object`](crate::Object) : Wraps a `BTreeMap<Value, Value>`, providing a key-value store
//!
//! A set of traits for performing operations on values is also provided:
//! - [`ArithmeticOperationExt`](crate::ArithmeticOperationExt) : Operations such as addition, subtraction, etc.
//! - [`BooleanOperationExt`](crate::BooleanOperationExt) : Equality, comparisons, as well as AND and OR
//! - [`BitwiseOperationExt`](crate::BitwiseOperationExt) : Bitwise operations such as AND, OR, XOR, etc.
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
