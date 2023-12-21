use crate::operations::*;
use crate::ValueType;
use thiserror::Error;

/// This type is used for all errors that can be returned by Polyvalue
#[derive(Error, Debug)]
pub enum Error {
    /// An error caused by a fault within Polyvalue
    #[error("internal error: {0}")]
    Internal(String),

    /// An error caused by attempting to use an operator on
    /// the wrong type
    #[error("could not perform arithmetic {operation} on {actual_type}")]
    UnsupportedOperation {
        /// Operation that caused the error
        operation: ArithmeticOperation,

        /// Type that caused the error
        actual_type: ValueType,
    },

    /// An error caused by attempting to overwrite a constant
    #[error("{src_type} cannot be converted to {dst_type}")]
    ValueConversion {
        /// Type that caused the error
        src_type: ValueType,

        /// Type that was requested
        dst_type: ValueType,
    },

    /// An error caused by attempting to use a value of the wrong type in a calculation
    #[error("expected {expected_type}, found {actual_type}")]
    ValueType {
        /// Value causing the error
        actual_type: ValueType,

        /// Type that was requested
        expected_type: ValueType,
    },

    /// An error caused by attempting to use an invalid object or array key
    #[error("undefined index {key}")]
    Index {
        /// Index that caused the error
        key: String,
    },

    /// An error caused by a calculation that resulted in an overflow
    #[error("arithmetic overflow")]
    Overflow,

    /// An error caused by parsing a value from a string
    #[error("invalid decimal value")]
    ParseDecimalError(#[from] fpdec::ParseDecimalError),

    /// An error caused by parsing a value from a string
    #[error("invalid float value")]
    ParseFloatError(#[from] std::num::ParseFloatError),

    /// An error caused by parsing a value from a string
    #[error("invalid integer value")]
    ParseIntError(#[from] std::num::ParseIntError),

    /// An error caused by parsing a Decimal
    #[error("invalid decimal value")]
    DecimalError(#[from] fpdec::DecimalError),
}
