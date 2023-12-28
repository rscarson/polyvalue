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
    /// If the operation is not supported on the given type,
    /// an `Error::UnsupportedOperation` will be returned
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{ArithmeticOperation, ArithmeticOperationExt};
    ///
    /// let a = Value::from(1);
    /// let b = Value::from(2);
    ///
    /// let result = Value::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap();
    /// assert_eq!(result, Value::from(3));
    /// ```
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error>
    where
        Self: Sized;

    /// Perform an arithmetic negation on a value
    /// This is equivalent to `arithmetic_op with ArithmeticOperation::Negate`
    /// but is provided for convenience
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{ArithmeticOperation, ArithmeticOperationExt};
    ///
    /// let a = Value::from(1);
    /// let result = a.arithmetic_neg().unwrap();
    /// assert_eq!(result, Value::from(-1));
    /// ```
    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
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
    /// If the operation is not supported on the given type,
    /// an `Error::UnsupportedOperation` will be returned
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{BitwiseOperation, BitwiseOperationExt};
    ///
    /// let a = Value::from(0x0F);
    /// let b = Value::from(0xF0);
    ///
    /// let result = Value::bitwise_op(&a, &b, BitwiseOperation::And).unwrap();
    /// assert_eq!(result, Value::from(0x00));
    /// ```
    fn bitwise_op(
        left: &Self,
        right: &Self,
        operation: BitwiseOperation,
    ) -> Result<Self, crate::Error>
    where
        Self: Sized;

    /// Perform a bitwise not on a value
    /// This is equivalent to `bitwise_op with BitwiseOperation::Not`
    /// but is provided for convenience
    ///
    /// Please note that a mask is applied to the result of this operation
    /// in order to ensure that the result is the same size as the input
    /// and correct for the way the underlying data is stored
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{BitwiseOperation, BitwiseOperationExt};
    ///
    /// let a = Value::from(0xA0);
    ///
    /// let result = a.bitwise_not().unwrap();
    /// assert_eq!(result, Value::from(0x5F));
    fn bitwise_not(&self) -> Result<Self, crate::Error>
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
    /// If the operation is not supported on the given type,
    /// an `Error::UnsupportedOperation` will be returned
    ///
    /// This type of operation will always return a boolean value
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{BooleanOperation, BooleanOperationExt};
    ///
    /// let a = Value::from(1);
    /// let b = Value::from(2);
    ///
    /// let result = Value::boolean_op(&a, &b, BooleanOperation::LT).unwrap();
    /// assert_eq!(result, Value::from(true));
    fn boolean_op(
        left: &Self,
        right: &Self,
        operation: BooleanOperation,
    ) -> Result<Value, crate::Error>
    where
        Self: Sized;

    /// Perform a boolean not on a value
    /// This is equivalent to `boolean_op with BooleanOperation::Not`
    /// but is provided for convenience
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{BooleanOperation, BooleanOperationExt};
    ///
    /// let a = Value::from(true);
    /// let result = a.boolean_not().unwrap();
    /// assert_eq!(result, Value::from(false));
    /// ```
    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized;
}

/// Indexing operation trait
pub trait IndexingOperationExt {
    /// Get a value from an index
    /// Returns a reference to the value, or an `Error::Index` if the index is not found
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::types::{Object};
    /// use polyvalue::operations::{IndexingOperationExt};
    ///
    /// let a = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
    /// let index = Value::from(1);
    /// let result = a.get_index(&index).unwrap();
    /// assert_eq!(result, &Value::from(2));
    ///
    /// let b = Object::try_from(vec![("a".into(), 1.into()), ("b".into(), 2.into())]);
    /// let index = Value::from("b");
    /// let result = b.get_index(&index).unwrap();
    /// assert_eq!(result, &Value::from(2));
    /// ```
    fn get_index(&self, index: &Value) -> Result<&Value, crate::Error>;

    /// Get values from one or more indices
    /// Returns a vector of references to the values, or an `Error::Index` if any of the indices are not found
    ///
    /// Acts as a convenience wrapper around `get_index` where array values are treated as a set of indices
    fn get_indices(&self, index: &Value) -> Result<Vec<&Value>, crate::Error>;

    /// Get a value from an index
    /// Returns a mutable reference to the value, or an `Error::Index` if the index is not found
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::types::{Object};
    /// use polyvalue::operations::{IndexingOperationExt};
    ///
    /// let mut b = Object::try_from(vec![("a".into(), 1.into()), ("b".into(), 2.into())]);
    /// let index = Value::from("b");
    /// let result = b.get_index_mut(&index).unwrap();
    /// *result = Value::from(3);
    ///
    /// assert_eq!(b.get_index(&index).unwrap(), &Value::from(3));
    /// ```
    fn get_index_mut(&mut self, index: &Value) -> Result<&mut Value, crate::Error>;

    /// Get values from one or more indices, mutably
    /// Returns a vector of references to the values, or an `Error::Index` if any of the indices are not found
    ///
    /// Acts as a convenience wrapper around `get_index` where array values are treated as a set of indices
    fn get_indices_mut(&mut self, index: &Value) -> Result<Vec<&mut Value>, crate::Error>;

    /// Set a value at an index
    /// Returns an `Error::Index` if the index is not found
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{IndexingOperationExt};
    ///
    /// let mut a = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
    /// let index = Value::from(1);
    /// a.set_index(&index, Value::from(4)).unwrap();
    /// assert_eq!(a.get_index(&index).unwrap(), &Value::from(4));
    /// ```
    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error>;
}

/// Matching operations
/// These operations are used to compare two values and return a boolean result
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MatchingOperation {
    /// Matches array or string contents
    Contains,

    /// Matches a string, array or regular expression
    Matches,

    /// Type-specific matching operations
    Is,

    /// This is a special case of `Matches` that matches the start of the target
    StartsWith,

    /// This is a special case of `Matches` that matches the end of the target
    EndsWith,
}

impl std::fmt::Display for MatchingOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MatchingOperation::Contains => write!(f, "contains"),
            MatchingOperation::Matches => write!(f, "matches"),
            MatchingOperation::Is => write!(f, "is"),
            MatchingOperation::StartsWith => write!(f, "startswith"),
            MatchingOperation::EndsWith => write!(f, "endswith"),
        }
    }
}

/// Trait for matching operations
pub trait MatchingOperationExt {
    /// Perform a matching operation on two values
    /// If the operation is not supported on the given type,
    /// an `Error::UnsupportedOperation` will be returned
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{MatchingOperation, MatchingOperationExt};
    ///
    /// let a = Value::from("Hello, world!");
    /// let b = Value::from("world");
    ///
    /// let result = Value::matching_op(&a, &b, MatchingOperation::Contains).unwrap();
    /// assert_eq!(result, Value::from(true));
    /// ```
    fn matching_op(
        container: &Self,
        pattern: &Value,
        operation: MatchingOperation,
    ) -> Result<Value, crate::Error>
    where
        Self: Sized;
}
