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
pub use currency::{Currency, CurrencyInner};
