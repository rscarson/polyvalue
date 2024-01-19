use crate::operations::*;
use crate::ValueType;
use thiserror::Error;

/// This type is used for all errors that can be returned by Polyvalue
#[derive(Error, Debug)]
pub enum Error {
    /// An error caused by attempting to use a value of the wrong type in a calculation
    #[error("Cannot not perform arithmetic {operation} on {actual_type}")]
    UnsupportedOperation {
        /// Operation that caused the error
        operation: ArithmeticOperation,

        /// Type that caused the error
        actual_type: ValueType,
    },

    /// An error caused by attempting to convert a value to a different type
    #[error("{src_type} cannot be converted to {dst_type}")]
    ValueConversion {
        /// Source type that caused the error
        src_type: ValueType,

        /// Destination type that caused the error
        dst_type: ValueType,
    },

    /// An error caused by attempting to use a value of the wrong type in a calculation
    #[error("Expected {expected_type}, found {actual_type}")]
    ValueType {
        /// Type that caused the error
        actual_type: ValueType,

        /// Expected type that caused the error
        expected_type: ValueType,
    },

    /// An error caused by attempting to use an invalid object or array key
    #[error("Undefined index {key}")]
    Index {
        /// Index that caused the error
        key: String,
    },

    /// An error caused by attempting to use an type as an object key
    #[error("Type {0} cannot be used as an object key")]
    InvalidTypeForKey(ValueType),

    /// An error caused by attempting to use an unsupported type
    #[error("Unrecognized type {0}. Expected one of [array, bool, currency, fixed, float, int, object, string, numeric, compound, any]")]
    UnrecognizedType(String),

    /// An error caused by a calculation that resulted in an overflow
    #[error("Arithmetic overflow")]
    Overflow,

    /// An error caused by parsing a value from a string
    #[error("Invalid fixed-point literal")]
    ParseDecimalError(#[from] fpdec::ParseDecimalError),

    /// An error caused by parsing a value from a string
    #[error("Invalid floatint-point literal")]
    ParseFloatError(#[from] std::num::ParseFloatError),

    /// An error caused by parsing a value from a string
    #[error("Invalid integer literal")]
    ParseIntError(#[from] std::num::ParseIntError),

    /// An error caused by parsing a value from a string
    #[error("Invalid range literal")]
    InvalidRange,

    /// An error caused by parsing a Decimal
    #[error("Given value cannot be converted to Decimal")]
    DecimalError(#[from] fpdec::DecimalError),

    /// An error caused by parsing a regex
    #[error("Invalid regex literal")]
    RegexError(#[from] regex::Error),

    /// An error caused by large allocations
    #[error("Memory allocation error")]
    TryReserveError(#[from] std::collections::TryReserveError),
}
