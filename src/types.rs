//! # Types
//! This module contains the subtypes available
//!
//! ## Available types
//! - [`Bool`](crate::types::Bool)
//! - [`Fixed`](crate::types::Fixed)
//! - [`Currency`](crate::types::Currency)
//! - [`Float`](crate::types::Float)
//! - [`Int`](crate::types::Int)
//! - [`Str`](crate::types::Str)
//! - [`Array`](crate::types::Array)
//! - [`Object`](crate::types::Object)
//!
//! See the individual types for more information.
//!
//! All subtypes wrap an inner type, which is accessible via the `inner()` method.
//! and for most types is defined as a type alias, such as [`IntInner`](crate::types::IntInner).
//!
//! ## Type conversion
//! All types implement the [`TryFrom`](std::convert::From) trait, allowing them to be converted
//! to and from the [`Value`](crate::Value) type.
//!
//! Any of the operations listed in [operations](crate::operations) can be performed on 2 values of
//! the same type, or on Value directly, which will determine the best type to use for the operation
//! and attempt to convert both values to that type.
//!
mod array;
pub use array::{Array, ArrayInner};

mod bool;
pub use bool::Bool;

mod fixed;
pub use fixed::{Fixed, FixedInner};

mod float;
pub use float::{Float, FloatInner};

mod int;
pub use int::{Int, IntInner};

mod object;
pub use object::{Object, ObjectInner};

mod string;
pub use string::Str;

mod currency;
pub use currency::Currency;
