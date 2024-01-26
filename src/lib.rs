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
//! - [`Bool`](crate::types::Bool) : Wraps a `bool`
//! - [`Int`](crate::types::Int) : Wraps an `i64`
//! - [`Float`](crate::types::Float) : Wraps an `f64`
//! - [`Fixed`](crate::types::Fixed) : Wraps an `fpdec::Decimal`, a fixed-point decimal type
//! - [`Currency`](crate::types::Currency) : Wraps a `Fixed` and adds a currency symbol
//! - [`Str`](crate::types::Str) : Wraps a `String`
//! - [`Array`](crate::types::Array) : Wraps a `Vec<Value>`, providing an ordered set
//! - [`Object`](crate::types::Object) : Wraps a `BTreeMap<Value, Value>`, providing a key-value store
//!
//! A set of traits for performing operations on values is also provided:
//! - [`ArithmeticOperationExt`](crate::operations::ArithmeticOperationExt) : Operations such as addition, subtraction, etc.
//! - [`BooleanOperationExt`](crate::operations::BooleanOperationExt) : Equality, comparisons, as well as AND and OR
//! - [`BitwiseOperationExt`](crate::operations::BitwiseOperationExt) : Bitwise operations such as AND, OR, XOR, etc.
//! - [`IndexingOperationExt`](crate::operations::IndexingOperationExt) : Indexing into arrays, objects, ranges, and strings
//! - [`IndexingOperationExt`](crate::operations::IndexingOperationExt) : Indexing mutably into arrays and objects
//!
//! Note that while indexing into strings is supported, it is not provided through the `IndexOperationExt` trait.
//! This is because we return substrings references, which have additional constraints. See [`Str`](crate::types::Str) for more information.
//!
#![doc(html_root_url = "https://docs.rs/polyvalue/0.3.0")]
#![warn(missing_docs)]

#[macro_use]
mod macros;

mod inner_currency;
mod is_currency;

mod inner_object;

mod error;
pub use error::Error;

mod value;
pub use value::*;

pub mod operations;
pub mod types;

// We will export the fpdec crate as well, so that users can use it directly

/// Fixed-point decimal type used by [`Fixed`](crate::types::Fixed) and [`Currency`](crate::types::Currency)
/// See the [`fpdec`](https://docs.rs/fpdec) crate for more information
pub use fpdec;
