//! # Operations
//! The operations module contains all the operations that can be performed on a value.
//! Boolean operations can be performed on any value, by converting it to a boolean first.
//! Bitwise operations can be performed on any value, which can be converted to an integer.
//! Arithmetic operations can be performed on numeric values, and on strings (for some ops)
use crate::Value;

/// Available arithmetic operations
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ArithmeticOperation {
    /// Add two values, or concatenate two strings
    Add,

    /// Subtract two values, or remove a substring from a string
    Subtract,

    /// Multiply two values
    Multiply,

    /// Divide two values
    Divide,

    /// Modulo two values
    Modulo,

    /// Exponentiate two values
    Exponentiate,

    /// Negate a value
    Negate,
}

impl std::fmt::Display for ArithmeticOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArithmeticOperation::Add => write!(f, "add"),
            ArithmeticOperation::Subtract => write!(f, "sub"),
            ArithmeticOperation::Multiply => write!(f, "mul"),
            ArithmeticOperation::Divide => write!(f, "div"),
            ArithmeticOperation::Modulo => write!(f, "mod"),
            ArithmeticOperation::Exponentiate => write!(f, "exp"),
            ArithmeticOperation::Negate => write!(f, "neg"),
        }
    }
}

/// Trait for arithmetic operations
pub trait ArithmeticOperationExt {
    /// Perform an arithmetic operation on two values
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error>
    where
        Self: Sized;
}

/// Available bitwise operations
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BitwiseOperation {
    /// Perform a bitwise and
    And,

    /// Perform a bitwise or
    Or,

    /// Perform a bitwise xor
    Xor,

    /// Perform a left shift
    LeftShift,

    /// Perform a right shift
    RightShift,

    /// Perform a bitwise not
    Not,
}

impl std::fmt::Display for BitwiseOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BitwiseOperation::And => write!(f, "and"),
            BitwiseOperation::Or => write!(f, "or"),
            BitwiseOperation::Xor => write!(f, "xor"),
            BitwiseOperation::LeftShift => write!(f, "lshift"),
            BitwiseOperation::RightShift => write!(f, "rshift"),
            BitwiseOperation::Not => write!(f, "not"),
        }
    }
}

/// Trait for bitwise operations
pub trait BitwiseOperationExt {
    /// Perform a bitwise operation on two values
    fn bitwise_op(
        left: &Self,
        right: &Self,
        operation: BitwiseOperation,
    ) -> Result<Self, crate::Error>
    where
        Self: Sized;
}

/// Available boolean operations
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BooleanOperation {
    /// Perform a boolean and
    And,

    /// Perform a boolean or
    Or,

    /// Perform a less than comparison
    LT,

    /// Perform a greater than comparison
    GT,

    /// Perform a less than or equal to comparison
    LTE,

    /// Perform a greater than or equal to comparison
    GTE,

    /// Perform an equal to comparison
    EQ,

    /// Perform a not equal to comparison
    NEQ,

    /// Perform a boolean not
    Not,
}
impl std::fmt::Display for BooleanOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BooleanOperation::And => write!(f, "and"),
            BooleanOperation::Or => write!(f, "or"),
            BooleanOperation::LT => write!(f, "lt"),
            BooleanOperation::GT => write!(f, "gt"),
            BooleanOperation::LTE => write!(f, "lte"),
            BooleanOperation::GTE => write!(f, "gte"),
            BooleanOperation::EQ => write!(f, "eq"),
            BooleanOperation::NEQ => write!(f, "neq"),
            BooleanOperation::Not => write!(f, "not"),
        }
    }
}

/// Trait for boolean operations
pub trait BooleanOperationExt {
    /// Perform a boolean operation on two values
    fn boolean_op(
        left: &Self,
        right: &Self,
        operation: BooleanOperation,
    ) -> Result<Self, crate::Error>
    where
        Self: Sized;
}

/// Indexing operation trait
pub trait IndexingOperationExt {
    /// Get a value from an index
    fn get_index(&self, index: &Value) -> Result<&Value, crate::Error>;

    /// Get a value from an index, mutably
    fn get_index_mut(&mut self, index: &Value) -> Result<&mut Value, crate::Error>;

    /// Set a value at an index
    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error>;
}
