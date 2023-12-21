//! This module defines the `Value` type, and the `ValueTrait` trait.
//! The `Value` type is an enum that can hold any of the supported value types.
//!
use crate::operations::*;
use crate::types::*;
use crate::Error;
use serde::{Deserialize, Serialize};

/// A trait that all values must implement
/// It enforces a set of common traits and accessors
pub trait ValueTrait<T>:
    std::fmt::Display
    + std::fmt::Debug
    + Clone
    + PartialEq
    + PartialOrd
    + std::hash::Hash
    + Serialize
    + for<'a> Deserialize<'a>
    + Default
{
    /// Creates a new value from the given inner value
    fn new(inner: T) -> Self;

    /// Returns a reference to the inner value
    fn inner(&self) -> &T;

    /// Returns a mutable reference to the inner value
    fn inner_mut(&mut self) -> &mut T;
}

/// The set of types that can be used as values
/// Bool, Fixed, Float, Currency, Int, String, Array, Object represent real types
/// whereas Numeric, Compound, and Any are virtual types representing a set of types
///
/// Numeric is a set of Fixed, Float, Currency, and Int
/// Compound is a set of Array and Object
/// Any is a set of all types
///
/// When operations are performed on values, the type of the result is determined
/// using the following order of priority:
/// - Object
/// - Array
/// - String
/// - Fixed
/// - Float
/// - Int
/// - Bool
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash, Serialize, Deserialize)]
pub enum ValueType {
    /// A boolean value
    Bool,

    /// A fixed-point value
    Fixed,

    /// A floating-point value
    Float,

    /// A currency value
    Currency,

    /// An integer value
    Int,

    /// A string value
    String,

    /// An array value
    Array,

    /// An object value
    Object,

    /// A numeric value (fixed, float, currency, or int)
    Numeric,

    /// A compound value (array or object)
    Compound,

    /// Any value
    Any,
}

impl std::fmt::Display for ValueType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueType::Bool => write!(f, "bool"),
            ValueType::Fixed => write!(f, "fixed"),
            ValueType::Float => write!(f, "float"),
            ValueType::Currency => write!(f, "currency"),
            ValueType::Int => write!(f, "int"),
            ValueType::String => write!(f, "string"),
            ValueType::Array => write!(f, "array"),
            ValueType::Object => write!(f, "object"),
            ValueType::Numeric => write!(f, "numeric"),
            ValueType::Compound => write!(f, "object or array"),
            ValueType::Any => write!(f, "any"),
        }
    }
}

impl From<&str> for ValueType {
    fn from(s: &str) -> Self {
        match s {
            "Bool" => ValueType::Bool,
            "Fixed" => ValueType::Fixed,
            "Float" => ValueType::Float,
            "Currency" => ValueType::Currency,
            "Int" => ValueType::Int,
            "String" => ValueType::String,
            "Array" => ValueType::Array,
            "Object" => ValueType::Object,
            "Numeric" => ValueType::Numeric,
            "Compound" => ValueType::Compound,
            _ => ValueType::Any,
        }
    }
}

/// Main value type
/// This is an enum that can hold any of the supported value types
#[derive(Clone, Hash, Serialize, Deserialize, Debug, Eq)]
pub enum Value {
    /// A boolean value
    Bool(Bool),

    /// A fixed-point value
    Fixed(Fixed),

    /// A floating-point value
    Float(Float),

    /// A currency value
    Currency(Currency),

    /// An integer value
    Int(Int),

    /// A string value
    String(Str),

    /// An array value
    Array(Array),

    /// An object value
    Object(Object),
}

impl Value {
    /// Resolves the type of two values based on a priority system.
    /// If successful, both returned values are guaranteed to be of
    /// the same type
    ///
    /// For details on type resolution, see [`Value::type_for_comparison`]
    ///
    /// # Example
    /// ```rust
    /// use polyvalue::Value;
    /// use polyvalue::ValueType;
    /// use polyvalue::types::Int;
    ///
    /// let a = Value::from(1.0);
    /// let b = Value::from(2);
    /// let (a, b) = a.resolve(&b).expect("Could not resolve types");
    /// assert!(a.own_type() == ValueType::Float);
    /// assert!(b.own_type() == ValueType::Float);
    /// ```
    pub fn resolve(&self, other: &Self) -> Result<(Value, Value), Error> {
        let values = match self.type_for_comparison(other) {
            ValueType::Bool => (
                Bool::try_from(self.clone())?.into(),
                Bool::try_from(other.clone())?.into(),
            ),

            ValueType::Fixed => (
                Fixed::try_from(self.clone())?.into(),
                Fixed::try_from(other.clone())?.into(),
            ),

            ValueType::Float => (
                Float::try_from(self.clone())?.into(),
                Float::try_from(other.clone())?.into(),
            ),

            ValueType::Currency => {
                let values: (Currency, Currency) = (
                    Currency::try_from(self.clone())?,
                    Currency::try_from(other.clone())?,
                );

                // Resolve symbols and precisions too
                let values = values.0.resolve(&values.1);

                (values.0.into(), values.1.into())
            }

            ValueType::Int => (
                Int::try_from(self.clone())?.into(),
                Int::try_from(other.clone())?.into(),
            ),

            ValueType::String => (
                Str::try_from(self.clone())?.into(),
                Str::try_from(other.clone())?.into(),
            ),

            ValueType::Array => (
                Array::try_from(self.clone())?.into(),
                Array::try_from(other.clone())?.into(),
            ),

            ValueType::Object => (
                Object::try_from(self.clone())?.into(),
                Object::try_from(other.clone())?.into(),
            ),

            _ => unreachable!(),
        };

        Ok(values)
    }

    /// Returns the type of the value
    ///
    /// # Example
    /// ```rust
    /// use polyvalue::Value;
    /// use polyvalue::ValueType;
    ///
    /// let value = Value::from(1.0);
    /// assert!(value.own_type() == ValueType::Float);
    /// ```
    pub fn own_type(&self) -> ValueType {
        match self {
            Value::Bool(_) => ValueType::Bool,
            Value::Fixed(_) => ValueType::Fixed,
            Value::Float(_) => ValueType::Float,
            Value::Currency(_) => ValueType::Currency,
            Value::Int(_) => ValueType::Int,
            Value::String(_) => ValueType::String,
            Value::Array(_) => ValueType::Array,
            Value::Object(_) => ValueType::Object,
        }
    }

    /// returns true if either value is of the given type
    ///
    /// # Example
    /// ```rust
    /// use polyvalue::Value;
    /// use polyvalue::ValueType;
    ///
    /// let a = Value::from(1.0);
    /// let b = Value::from(2);
    /// assert!(a.either_type(&b, ValueType::Float));
    /// ```
    pub fn either_type(&self, other: &Self, match_on: ValueType) -> bool {
        self.is_a(match_on) || other.is_a(match_on)
    }

    /// Resolves a value to the given type
    /// Use with the types defined in [`crate::types`]
    ///
    /// Useful for enforcing a specific type, when you still wish to allow type-cooersion
    /// Float to Int, for example
    ///
    /// # Example
    /// ```rust
    /// use polyvalue::Value;
    /// use polyvalue::types::Int;
    ///
    /// let value = Value::from(1.0);
    /// let int = value.as_a::<Int>().expect("Value could not be converted to int!");
    /// ```
    pub fn as_a<T: std::convert::TryFrom<Value, Error = Error>>(&self) -> Result<T, Error> {
        T::try_from(self.clone())
    }

    /// Returns true if the value is of the given type
    /// Use with the [`ValueType`] enum
    ///
    /// # Example
    /// ```rust
    /// use polyvalue::Value;
    /// use polyvalue::ValueType;
    ///
    /// let value = Value::from(1.0);
    /// assert!(!value.is_a(ValueType::Int));
    /// ```
    pub fn is_a(&self, type_name: ValueType) -> bool {
        match type_name {
            ValueType::Numeric => {
                Int::try_from(self.clone()).is_ok()
                    || Float::try_from(self.clone()).is_ok()
                    || Fixed::try_from(self.clone()).is_ok()
                    || Currency::try_from(self.clone()).is_ok()
            }
            ValueType::Compound => {
                Array::try_from(self.clone()).is_ok() || Object::try_from(self.clone()).is_ok()
            }
            ValueType::Any => true,

            _ => self.own_type() == type_name,
        }
    }

    /// Resolves a value to the given type
    /// Will fail if the value cannot be converted to the given type,
    /// or if type_name is not a real type (Numeric, Compound, or Any)
    ///
    /// Similar to [`Value::as_a`], but for type names in the [`ValueType`] enum
    /// intead of types in the [`crate::types`] module
    ///
    /// # Example
    /// ```rust
    /// use polyvalue::Value;
    /// use polyvalue::ValueType;
    ///
    /// let value = Value::from(1.0);
    /// let int = value.as_type(ValueType::Int).expect("Value could not be converted to int!");
    /// ```
    pub fn as_type(&self, type_name: ValueType) -> Result<Value, Error> {
        let value = match type_name {
            ValueType::Bool => Bool::try_from(self.clone())?.into(),
            ValueType::Fixed => Fixed::try_from(self.clone())?.into(),
            ValueType::Float => Float::try_from(self.clone())?.into(),
            ValueType::Currency => Currency::try_from(self.clone())?.into(),
            ValueType::Int => Int::try_from(self.clone())?.into(),
            ValueType::String => Str::try_from(self.clone())?.into(),
            ValueType::Array => Array::try_from(self.clone())?.into(),
            ValueType::Object => Object::try_from(self.clone())?.into(),
            _ => {
                return Err(Error::ValueConversion {
                    src_type: self.own_type(),
                    dst_type: type_name,
                })
            }
        };
        Ok(value)
    }

    /// Resolves the type of two values based on a priority system
    /// in order to determine how 2 values should be compared
    ///
    /// If both values are the same type, return that type
    /// Otherwise, cooerce both values to the same type using
    /// the order of priority:
    /// - Object
    /// - Array
    /// - String
    /// - Fixed
    /// - Float
    /// - Int
    /// - Bool
    pub fn type_for_comparison(&self, other: &Self) -> ValueType {
        if self.own_type() == other.own_type() {
            return self.own_type();
        } else if self.either_type(other, ValueType::Object) {
            return ValueType::Object;
        } else if self.either_type(other, ValueType::Array) {
            return ValueType::Array;
        } else if self.either_type(other, ValueType::String) {
            return ValueType::String;
        } else if self.either_type(other, ValueType::Fixed) {
            return ValueType::Fixed;
        } else if self.either_type(other, ValueType::Float) {
            return ValueType::Float;
        } else if self.either_type(other, ValueType::Currency) {
            return ValueType::Currency;
        } else if self.either_type(other, ValueType::Int) {
            return ValueType::Int;
        } else if self.either_type(other, ValueType::Bool) {
            return ValueType::Bool;
        } else {
            panic!(
                "Type {:?} was not recognized; this should never happen",
                self
            );
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(v) => write!(f, "{}", v),
            Value::Fixed(v) => write!(f, "{}", v),
            Value::Float(v) => write!(f, "{}", v),
            Value::Currency(v) => write!(f, "{}", v),
            Value::Int(v) => write!(f, "{}", v),
            Value::String(v) => write!(f, "{}", v),
            Value::Array(v) => write!(f, "{}", v),
            Value::Object(v) => write!(f, "{}", v),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        if let Ok((a, b)) = self.resolve(other) {
            match (a, b) {
                (Value::Bool(a), Value::Bool(b)) => a == b,
                (Value::Fixed(a), Value::Fixed(b)) => a == b,
                (Value::Float(a), Value::Float(b)) => a == b,
                (Value::Currency(a), Value::Currency(b)) => a == b,
                (Value::Int(a), Value::Int(b)) => a == b,
                (Value::String(a), Value::String(b)) => a == b,
                (Value::Array(a), Value::Array(b)) => a == b,
                (Value::Object(a), Value::Object(b)) => a == b,
                _ => false,
            }
        } else {
            false
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if let Ok((a, b)) = self.resolve(other) {
            match a.own_type() {
                ValueType::Bool => Bool::try_from(a)
                    .unwrap()
                    .partial_cmp(&Bool::try_from(b).unwrap()),
                ValueType::Fixed => Fixed::try_from(a)
                    .unwrap()
                    .partial_cmp(&Fixed::try_from(b).unwrap()),
                ValueType::Float => Float::try_from(a)
                    .unwrap()
                    .partial_cmp(&Float::try_from(b).unwrap()),
                ValueType::Currency => Currency::try_from(a)
                    .unwrap()
                    .partial_cmp(&Currency::try_from(b).unwrap()),
                ValueType::Int => Int::try_from(a)
                    .unwrap()
                    .partial_cmp(&Int::try_from(b).unwrap()),
                ValueType::String => Str::try_from(a)
                    .unwrap()
                    .partial_cmp(&Str::try_from(b).unwrap()),
                ValueType::Array => Array::try_from(a)
                    .unwrap()
                    .partial_cmp(&Array::try_from(b).unwrap()),
                ValueType::Object => Object::try_from(a)
                    .unwrap()
                    .partial_cmp(&Object::try_from(b).unwrap()),

                _ => None,
            }
        } else {
            None
        }
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if let Some(ord) = self.partial_cmp(other) {
            ord
        } else {
            // Only need to worry about those conversions that
            // can fail - meaning compound types
            // The other one would be string, but that's handled
            // by the fact that such comparisons are always done
            // as string <-> string
            match (self.own_type(), other.own_type()) {
                // This will be a comparison between an array and a singleton
                // where len > 1 - therefore the array is always greater
                (ValueType::Array, _) => std::cmp::Ordering::Greater,
                (_, ValueType::Array) => std::cmp::Ordering::Less,

                // This will be a comparison between an object and a singleton
                // where len > 1 - therefore the object is always greater
                (ValueType::Object, _) => std::cmp::Ordering::Greater,
                (_, ValueType::Object) => std::cmp::Ordering::Less,

                _ => unreachable!(),
            }
        }
    }
}

impl BooleanOperationExt for Value {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Self, Error> {
        let (left, right) = left.resolve(right)?;
        match (left, right) {
            (Value::Bool(l), Value::Bool(r)) => Bool::boolean_op(&l, &r, operation).map(Into::into),
            (Value::Fixed(l), Value::Fixed(r)) => {
                Fixed::boolean_op(&l, &r, operation).map(Into::into)
            }
            (Value::Float(l), Value::Float(r)) => {
                Float::boolean_op(&l, &r, operation).map(Into::into)
            }
            (Value::Currency(l), Value::Currency(r)) => {
                Currency::boolean_op(&l, &r, operation).map(Into::into)
            }
            (Value::Int(l), Value::Int(r)) => Int::boolean_op(&l, &r, operation).map(Into::into),
            (Value::String(l), Value::String(r)) => {
                Str::boolean_op(&l, &r, operation).map(Into::into)
            }
            (Value::Array(l), Value::Array(r)) => {
                Array::boolean_op(&l, &r, operation).map(Into::into)
            }
            (Value::Object(l), Value::Object(r)) => {
                Object::boolean_op(&l, &r, operation).map(Into::into)
            }
            _ => Err(Error::Internal(
                "Invalid type combination during boolean operation".to_string(),
            )),
        }
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Self::boolean_op(self, &self.clone(), BooleanOperation::Not)
    }
}

impl ArithmeticOperationExt for Value {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, Error> {
        let (left, right) = left.resolve(right)?;
        match (left, right) {
            (Value::Bool(l), Value::Bool(r)) => {
                Bool::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            (Value::Fixed(l), Value::Fixed(r)) => {
                Fixed::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            (Value::Float(l), Value::Float(r)) => {
                Float::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            (Value::Currency(l), Value::Currency(r)) => {
                Currency::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            (Value::Int(l), Value::Int(r)) => Int::arithmetic_op(&l, &r, operation).map(Into::into),
            (Value::String(l), Value::String(r)) => {
                Str::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            (Value::Array(l), Value::Array(r)) => {
                Array::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            (Value::Object(l), Value::Object(r)) => {
                Object::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            _ => Err(Error::Internal(
                "Invalid type combination during arithmetic operation".to_string(),
            )),
        }
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Self::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }
}

impl BitwiseOperationExt for Value {
    fn bitwise_op(
        left: &Self,
        right: &Self,
        operation: BitwiseOperation,
    ) -> Result<Self, crate::Error> {
        let left = *Int::try_from(left.clone())?.inner();
        let right = *Int::try_from(right.clone())?.inner();

        let result = match operation {
            BitwiseOperation::And => left & right,
            BitwiseOperation::Or => left | right,
            BitwiseOperation::Xor => left ^ right,
            BitwiseOperation::LeftShift => left << right,
            BitwiseOperation::RightShift => left >> right,

            // This is to remove the side-effects of the way the ints are stored
            BitwiseOperation::Not => left ^ (std::u64::MAX >> left.leading_zeros()) as IntInner,
        };

        Ok(result.into())
    }

    fn bitwise_not(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Self::bitwise_op(self, &self.clone(), BitwiseOperation::Not)
    }
}

impl IndexingOperationExt for Value {
    fn get_index(&self, index: &Value) -> Result<&Value, crate::Error> {
        match self {
            Value::Array(v) => v.get_index(index),
            Value::Object(v) => v.get_index(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }

    fn get_indices(&self, index: &Value) -> Result<Vec<&Value>, crate::Error> {
        match self {
            Value::Array(v) => v.get_indices(index),
            Value::Object(v) => v.get_indices(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }

    fn get_index_mut(&mut self, index: &Value) -> Result<&mut Value, crate::Error> {
        match self {
            Value::Array(v) => v.get_index_mut(index),
            Value::Object(v) => v.get_index_mut(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }

    fn get_indices_mut(&mut self, index: &Value) -> Result<Vec<&mut Value>, crate::Error> {
        match self {
            Value::Array(v) => v.get_indices_mut(index),
            Value::Object(v) => v.get_indices_mut(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        match self {
            Value::Array(v) => v.set_index(index, value),
            Value::Object(v) => v.set_index(index, value),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }
}
