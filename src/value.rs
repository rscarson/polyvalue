use crate::operations::*;
use crate::types::*;
use crate::Error;
use serde::{Deserialize, Serialize};

/// A trait that all values must implement
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
    /// Resolves the type of two values based on a priority system:
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
    pub fn resolve(&self, other: &Self) -> Result<(Value, Value), Error> {
        let values = match self.resolve_types(other) {
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
                let mut values: (Currency, Currency) = (
                    Currency::try_from(self.clone())?,
                    Currency::try_from(other.clone())?,
                );
                let symbol = if values.0.symbol().is_some() {
                    values.0.symbol().clone()
                } else {
                    values.1.symbol().clone()
                };

                values.0.set_symbol(symbol.clone());
                values.1.set_symbol(symbol.clone());
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

    /// Returns the type of the value
    pub fn either_type(&self, other: &Self, match_on: ValueType) -> bool {
        self.own_type() == match_on || other.own_type() == match_on
    }

    /// Resolves the type of two values based on a priority system:
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
    pub fn resolve_types(&self, other: &Self) -> ValueType {
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
            // Unreachable
            return ValueType::Any;
        }
    }

    /// Resolves a value to the given type
    pub fn resolve_to(&self, type_name: ValueType) -> Result<Value, Error> {
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

    /// Returns true if the value is of the given type
    pub fn matches_type(&self, type_name: ValueType) -> bool {
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

            _ => self.resolve_to(type_name).is_ok(),
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
            match a.own_type() {
                ValueType::Bool => Bool::try_from(a).unwrap() == Bool::try_from(b).unwrap(),
                ValueType::Fixed => Fixed::try_from(a).unwrap() == Fixed::try_from(b).unwrap(),
                ValueType::Float => Float::try_from(a).unwrap() == Float::try_from(b).unwrap(),
                ValueType::Currency => {
                    Currency::try_from(a).unwrap() == Currency::try_from(b).unwrap()
                }
                ValueType::Int => Int::try_from(a).unwrap() == Int::try_from(b).unwrap(),
                ValueType::String => Str::try_from(a).unwrap() == Str::try_from(b).unwrap(),
                ValueType::Array => Array::try_from(a).unwrap() == Array::try_from(b).unwrap(),
                ValueType::Object => Object::try_from(a).unwrap() == Object::try_from(b).unwrap(),

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
        let left = *Bool::try_from(left.clone())?.inner();
        let right = *Bool::try_from(right.clone())?.inner();
        let result = match operation {
            BooleanOperation::And => left && right,
            BooleanOperation::Or => left || right,
            BooleanOperation::LT => left < right,
            BooleanOperation::GT => left > right,
            BooleanOperation::LTE => left <= right,
            BooleanOperation::GTE => left >= right,
            BooleanOperation::EQ => left == right,
            BooleanOperation::NEQ => left != right,
            BooleanOperation::Not => !left,
        };

        Ok(result.into())
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
            _ => Err(Error::UnsupportedOperation {
                operation: operation,
                actual_type: ValueType::Any,
            }),
        }
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
            BitwiseOperation::Not => !left,
        };

        Ok(result.into())
    }
}

impl IndexingOperationExt for Value {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        match self {
            Value::String(v) => v.get_index(index),
            Value::Array(v) => v.get_index(index),
            Value::Object(v) => v.get_index(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        match self {
            Value::String(v) => v.set_index(index, value),
            Value::Array(v) => v.set_index(index, value),
            Value::Object(v) => v.set_index(index, value),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }
}
