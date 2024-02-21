//! # Operations
//! The operations module contains all the operations that can be performed on a value.
//! Boolean operations can be performed on any value, by converting it to a boolean first.
//! Bitwise operations can be performed on any value, which can be converted to an integer.
//! Arithmetic operations can be performed on numeric values, and on strings (for some ops)
//! Indexing operations can be performed on arrays, objects, strings, and ranges
//! Mutable indexing operations can be performed on arrays and objects
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

    /// Check if an operation is supported on a given type
    /// This is useful for checking if a given operation is supported
    /// before attempting to perform it
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value, operations::{ArithmeticOperationExt, ArithmeticOperation}};
    ///
    /// let a = Value::from(1);
    /// let b = Value::from(2);
    ///
    /// assert!(Value::is_operator_supported(&a, &b, ArithmeticOperation::Add));
    /// ````
    fn is_operator_supported(&self, other: &Self, operation: ArithmeticOperation) -> bool;
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
    /// let a = Value::u8(0xFF);
    ///
    /// let result = a.bitwise_not().unwrap();
    /// assert_eq!(result, Value::u8(0x00));
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

/// A trait for indexing operations that can mutate the value
pub trait IndexingMutationExt {
    /// Get a value from an index
    /// Returns a mutable reference to the value, or an `Error::Index` if the index is not found
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::types::{Object};
    /// use polyvalue::operations::{IndexingOperationExt, IndexingMutationExt};
    ///
    /// let mut b = Object::try_from(vec![("a".into(), 1.into()), ("b".into(), 2.into())]).unwrap();
    /// let index = Value::from("b");
    /// let result = b.get_index_mut(&index).unwrap();
    /// *result = Value::from(3);
    ///
    /// assert_eq!(b.get_index(&index).unwrap(), Value::from(3));
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
    /// use polyvalue::operations::{IndexingOperationExt, IndexingMutationExt};
    ///
    /// let mut a = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
    /// let index = Value::from(1);
    /// a.set_index(&index, Value::from(4)).unwrap();
    /// assert_eq!(a.get_index(&index).unwrap(), Value::from(4));
    /// ```
    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error>;

    /// Insert a value at an index
    /// Returns an `Error::Index` if the index is out of bounds
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{IndexingOperationExt, IndexingMutationExt};
    ///
    /// let mut a = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
    /// let index = Value::from(1);
    /// a.insert_at(&index, Value::from(4)).unwrap();
    /// assert_eq!(a.get_index(&index).unwrap(), Value::from(4));
    /// ```
    fn insert_at(&mut self, index: &Value, value: Value) -> Result<(), crate::Error>;

    /// Delete a value at an index
    /// Returns an `Error::Index` if the index is not found
    ///
    /// # Examples
    /// ```
    /// use polyvalue::{Value};
    /// use polyvalue::operations::{IndexingOperationExt, IndexingMutationExt};
    ///
    /// let mut a = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
    /// let index = Value::from(1);
    /// a.delete_index(&index).unwrap();
    /// ```
    fn delete_index(&mut self, index: &Value) -> Result<Value, crate::Error>;
}

/// Indexing operation trait
pub trait IndexingOperationExt {
    /// Get a value from an index
    /// Returns a value, or an `Error::Index` if the index is not found
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
    /// assert_eq!(result, Value::from(2));
    ///
    /// let b = Object::try_from(vec![("a".into(), 1.into()), ("b".into(), 2.into())]).unwrap();
    /// let index = Value::from("b");
    /// let result = b.get_index(&index).unwrap();
    /// assert_eq!(result, Value::from(2));
    /// ```
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error>;

    /// Get values from one or more indices
    /// Returns a vector of values, or an `Error::Index` if any of the indices are not found
    ///
    /// Acts as a convenience wrapper around `get_index` where array values are treated as a set of indices
    fn get_indices(&self, index: &Value) -> Result<Value, crate::Error>;
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_bitwise_display() {
        assert_eq!(BitwiseOperation::And.to_string(), "and");
        assert_eq!(BitwiseOperation::Or.to_string(), "or");
        assert_eq!(BitwiseOperation::Xor.to_string(), "xor");
        assert_eq!(BitwiseOperation::LeftShift.to_string(), "lshift");
        assert_eq!(BitwiseOperation::RightShift.to_string(), "rshift");
        assert_eq!(BitwiseOperation::Not.to_string(), "not");
    }

    #[test]
    fn test_boolean_display() {
        assert_eq!(BooleanOperation::And.to_string(), "and");
        assert_eq!(BooleanOperation::Or.to_string(), "or");
        assert_eq!(BooleanOperation::LT.to_string(), "lt");
        assert_eq!(BooleanOperation::GT.to_string(), "gt");
        assert_eq!(BooleanOperation::LTE.to_string(), "lte");
        assert_eq!(BooleanOperation::GTE.to_string(), "gte");
        assert_eq!(BooleanOperation::EQ.to_string(), "eq");
        assert_eq!(BooleanOperation::NEQ.to_string(), "neq");
        assert_eq!(BooleanOperation::Not.to_string(), "not");
    }

    #[test]
    fn test_arithmetic_display() {
        assert_eq!(ArithmeticOperation::Add.to_string(), "add");
        assert_eq!(ArithmeticOperation::Subtract.to_string(), "sub");
        assert_eq!(ArithmeticOperation::Multiply.to_string(), "mul");
        assert_eq!(ArithmeticOperation::Divide.to_string(), "div");
        assert_eq!(ArithmeticOperation::Modulo.to_string(), "mod");
        assert_eq!(ArithmeticOperation::Exponentiate.to_string(), "exp");
        assert_eq!(ArithmeticOperation::Negate.to_string(), "neg");
    }

    #[test]
    fn test_matching_display() {
        assert_eq!(MatchingOperation::Contains.to_string(), "contains");
        assert_eq!(MatchingOperation::Matches.to_string(), "matches");
        assert_eq!(MatchingOperation::Is.to_string(), "is");
        assert_eq!(MatchingOperation::StartsWith.to_string(), "startswith");
        assert_eq!(MatchingOperation::EndsWith.to_string(), "endswith");
    }
}
