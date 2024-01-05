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

impl TryFrom<&str> for ValueType {
    type Error = Error;
    fn try_from(s: &str) -> Result<Self, Error> {
        match s.to_lowercase().as_str() {
            "bool" => Ok(ValueType::Bool),
            "fixed" => Ok(ValueType::Fixed),
            "float" => Ok(ValueType::Float),
            "currency" => Ok(ValueType::Currency),
            "int" => Ok(ValueType::Int),
            "string" => Ok(ValueType::String),
            "array" => Ok(ValueType::Array),
            "object" => Ok(ValueType::Object),
            "numeric" => Ok(ValueType::Numeric),
            "compound" => Ok(ValueType::Compound),
            _ => Err(Error::UnrecognizedType(s.to_string())),
        }
    }
}

/// Main value type
/// This is an enum that can hold any of the supported value types
#[derive(Clone, Hash, Serialize, Deserialize, Debug, Eq)]
#[serde(untagged)]
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

impl TryFrom<serde_json::Value> for Value {
    type Error = Error;
    fn try_from(value: serde_json::Value) -> Result<Self, Self::Error> {
        match value {
            serde_json::Value::Null => Ok(Value::String(Str::from(""))),
            serde_json::Value::Bool(v) => Ok(Value::Bool(Bool::from(v))),
            serde_json::Value::String(v) => Ok(Value::String(Str::from(v))),
            serde_json::Value::Array(v) => Ok(v
                .iter()
                .map(|v| Value::try_from(v.clone()))
                .collect::<Result<Vec<_>, _>>()?
                .into()),
            serde_json::Value::Object(v) => {
                let mut object = ObjectInner::new();
                for (key, value) in v {
                    object.insert(Value::from(key), Value::try_from(value)?)?;
                }
                Ok(Value::Object(object.into()))
            }
            serde_json::Value::Number(v) => {
                if v.is_i64() {
                    Ok(Value::Int(Int::from(v.as_i64().unwrap())))
                } else if v.is_f64() {
                    Ok(Value::Float(Float::from(v.as_f64().unwrap())))
                } else {
                    Err(Error::UnrecognizedType(format!(
                        "Could not convert json number to value: {:?}",
                        v
                    )))
                }
            }
        }
    }
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
                self.own_type() == ValueType::Array || self.own_type() == ValueType::Object
            }
            ValueType::Any => true,

            _ => self.own_type() == type_name,
        }
    }

    /// Resolves a value to the given type
    /// Will fail if the value cannot be converted to the given type,
    ///
    /// For virtual types, the highest-priority match will be used
    /// For any, the input value will be returned
    /// For numeric, the value will be converted to fixed
    /// For compound, the value will be converted to object
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
            ValueType::Fixed | ValueType::Numeric => Fixed::try_from(self.clone())?.into(),
            ValueType::Float => Float::try_from(self.clone())?.into(),
            ValueType::Currency => Currency::try_from(self.clone())?.into(),
            ValueType::Int => Int::try_from(self.clone())?.into(),
            ValueType::String => Str::try_from(self.clone())?.into(),
            ValueType::Array => Array::try_from(self.clone())?.into(),
            ValueType::Object | ValueType::Compound => Object::try_from(self.clone())?.into(),

            ValueType::Any => self.clone(),
        };
        Ok(value)
    }

    /// Resolves the type of two values based on a priority system
    /// in order to determine how 2 values should be compared
    ///
    /// The priority system is designed to prevent loss of information
    /// when comparing values of different types
    /// For example, Object -> Array would lose information on non-numeric keys
    /// Wheres Array -> Object would not
    ///
    /// If both values are the same type, return that type
    /// Otherwise, cooerce both values to the same type using
    /// the order of priority:
    /// - Object
    /// - Array
    /// - String
    /// - Currency
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
        } else if self.either_type(other, ValueType::Currency) {
            return ValueType::Currency;
        } else if self.either_type(other, ValueType::Fixed) {
            return ValueType::Fixed;
        } else if self.either_type(other, ValueType::Float) {
            return ValueType::Float;
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

impl MatchingOperationExt for Value {
    fn matching_op(
        container: &Self,
        pattern: &Value,
        operation: MatchingOperation,
    ) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        // Special case for type matching
        if operation == MatchingOperation::Is {
            let type_name = pattern.as_a::<Str>()?;
            return Ok(Value::Bool(Bool::new(
                &container.own_type().to_string() == type_name.inner(),
            )));
        }

        if container.is_a(ValueType::Compound) {
            Array::matching_op(&container.as_a::<Array>()?, pattern, operation)
        } else {
            Str::matching_op(&container.as_a::<Str>()?, pattern, operation)
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

    fn delete_index(&mut self, index: &Value) -> Result<Value, crate::Error> {
        match self {
            Value::Array(v) => v.delete_index(index),
            Value::Object(v) => v.delete_index(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }
}

//
// Tests
//

#[cfg(test)]
mod test {
    use super::*;
    use fpdec::Decimal;

    #[test]
    fn test_matching() {
        // lets only test 'is' for now
        let value = Value::from(1.0);
        let pattern = Value::from("float");
        let result = Value::matching_op(&value, &pattern, MatchingOperation::Is)
            .expect("Could not perform matching operation");
        assert_eq!(result, Value::from(true));
    }

    #[test]
    fn test_resolve() {
        let a = Value::from(1.0);
        let b = Value::from(2);
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Float);
        assert!(b.own_type() == ValueType::Float);

        let a = Value::from(1);
        let b = Value::from(2);
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Int);
        assert!(b.own_type() == ValueType::Int);

        let a = Value::from("abc");
        let b = Value::from(2);
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::String);
        assert!(b.own_type() == ValueType::String);

        let a = Value::from(1);
        let b = Value::from(vec![Value::from(1)]);
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Array);
        assert!(b.own_type() == ValueType::Array);

        let a = Value::from(vec![Value::from(1)]);
        let b = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Object);
        assert!(b.own_type() == ValueType::Object);

        let a = Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO)));
        let b = Value::from(Fixed::from(Decimal::ZERO));
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Currency);
        assert!(b.own_type() == ValueType::Currency);
    }

    #[test]
    fn test_own_type() {
        assert_eq!(Value::from(false).own_type(), ValueType::Bool);
        assert_eq!(Value::from(1.0).own_type(), ValueType::Float);
        assert_eq!(Value::from(1).own_type(), ValueType::Int);
        assert_eq!(Value::from("abc").own_type(), ValueType::String);
        assert_eq!(
            Value::from(vec![Value::from(1)]).own_type(),
            ValueType::Array
        );
        assert_eq!(
            Value::try_from(vec![(Value::from("a"), Value::from(1))])
                .unwrap()
                .own_type(),
            ValueType::Object
        );

        assert_eq!(
            Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO))).own_type(),
            ValueType::Currency
        );

        assert_eq!(
            Value::from(Fixed::from(Decimal::ZERO)).own_type(),
            ValueType::Fixed
        );
    }

    #[test]
    fn either_type() {
        let a = Value::from(1.0);
        let b = Value::from(2);
        assert!(a.either_type(&b, ValueType::Float));

        let a = Value::from(1);
        let b = Value::from(2);
        assert!(a.either_type(&b, ValueType::Int));

        let a = Value::from("abc");
        let b = Value::from(2);
        assert!(a.either_type(&b, ValueType::String));

        let a = Value::from(vec![Value::from(1)]);
        let b = Value::from(2);
        assert!(a.either_type(&b, ValueType::Compound));
    }

    #[test]
    fn test_as_a() {
        let value = Value::from(1.0);
        let int = value
            .as_a::<Int>()
            .expect("Value could not be converted to int!");
        assert_eq!(int, Int::from(1));

        let value = Value::from(1);
        let float = value
            .as_a::<Float>()
            .expect("Value could not be converted to float!");
        assert_eq!(float, Float::from(1.0));

        let value = Value::from("error");
        value
            .as_a::<Float>()
            .expect_err("Value should not be convertible to float!");

        let value = Value::from(1.0);
        let object = value
            .as_a::<Object>()
            .expect("Value could not be converted to object!");
        assert_eq!(
            object,
            Object::try_from(vec![(Value::from("0"), Value::from(1.0))]).unwrap()
        );
    }

    #[test]
    fn test_is_a() {
        let value = Value::from(1.0);
        assert!(!value.is_a(ValueType::Int));

        let value = Value::from(1);
        assert!(value.is_a(ValueType::Int));

        let value = Value::from("abc");
        assert!(value.is_a(ValueType::String));

        let value = Value::from(vec![Value::from(1)]);
        assert!(value.is_a(ValueType::Array));
        assert!(value.is_a(ValueType::Compound));
        assert!(!value.is_a(ValueType::Object));
    }

    #[test]
    fn test_as_type() {
        let value = Value::from(1.0);
        let int = value
            .as_type(ValueType::Int)
            .expect("Value could not be converted to int!");
        assert_eq!(int, Value::from(1));

        let value = Value::from(1);
        let float = value
            .as_type(ValueType::Float)
            .expect("Value could not be converted to float!");
        assert_eq!(float, Value::from(1.0));

        let value = Value::from("error");
        value
            .as_type(ValueType::Float)
            .expect_err("Value should not be convertible to float!");

        let value = Value::from(1.0);
        let value = value
            .as_type(ValueType::Compound)
            .expect("Value could not be converted to compound!");
        assert_eq!(
            value,
            Value::try_from(vec![(Value::from("0"), Value::from(1.0))]).unwrap()
        );

        let value = Value::from(1.0);
        let value = value
            .as_type(ValueType::Any)
            .expect("Value could not be converted to any!");
        assert_eq!(value, Value::from(1.0));
    }

    #[test]
    fn test_type_for_comparison() {
        // int/float = float
        let a = Value::from(1.0);
        let b = Value::from(2);
        assert_eq!(a.type_for_comparison(&b), ValueType::Float);

        // int/bool = int
        let a = Value::from(1);
        let b = Value::from(true);
        assert_eq!(a.type_for_comparison(&b), ValueType::Int);

        // int/string = string
        let a = Value::from(1);
        let b = Value::from("abc");
        assert_eq!(a.type_for_comparison(&b), ValueType::String);

        // int/array = array
        let a = Value::from(1);
        let b = Value::from(vec![Value::from(1)]);
        assert_eq!(a.type_for_comparison(&b), ValueType::Array);

        // array/object = object
        let a = Value::from(vec![Value::from(1)]);
        let b = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        assert_eq!(a.type_for_comparison(&b), ValueType::Object);

        // int/currency = currency
        let a = Value::from(1);
        let b = Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO)));
        assert_eq!(a.type_for_comparison(&b), ValueType::Currency);

        // fixed/currency = fixed
        let a = Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO)));
        let b = Value::from(Fixed::from(Decimal::ZERO));
        assert_eq!(a.type_for_comparison(&b), ValueType::Currency);
    }

    #[test]
    fn test_display() {
        assert_eq!(Value::from(1.0).to_string(), "1.0");
        assert_eq!(Value::from(1).to_string(), "1");
        assert_eq!(Value::from("abc").to_string(), "abc");
        assert_eq!(Value::from(vec![Value::from(1)]).to_string(), "[1]");
        assert_eq!(
            Value::try_from(vec![(Value::from("a"), Value::from(1))])
                .unwrap()
                .to_string(),
            "{a: 1}"
        );

        assert_eq!(Value::from(true).to_string(), "true");
        assert_eq!(Value::from(false).to_string(), "false");

        assert_eq!(
            Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO))).to_string(),
            "$0.00"
        );
    }

    #[test]
    fn test_ord() {
        // 2 of the same - string to string
        assert!(Value::from("abc") < Value::from("def"));
        assert!(Value::from("def") > Value::from("abc"));
        assert!(Value::from("abc") == Value::from("abc"));

        // 2 different, but comparable - float to int
        assert!(Value::from(1.0) < Value::from(2));
        assert!(Value::from(2.0) > Value::from(1));
        assert!(Value::from(1.0) == Value::from(1));

        // int to string should work as string to string
        assert!(Value::from(1) < Value::from("def"));
        assert!(Value::from(1) == Value::from("1"));

        // 2 different, not comparable - big array to int
        assert!(Value::from(vec![Value::from(1), Value::from(2)]) > Value::from(1));

        // object to array
        assert!(
            Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap()
                > Value::from(vec![Value::from(1), Value::from(2)])
        );
    }

    #[test]
    fn test_eq() {
        // 2 of the same - string to string
        assert_eq!(Value::from("abc"), Value::from("abc"));
        assert_ne!(Value::from("cba"), Value::from("abc"));

        // 2 different, but comparable - float to int
        assert_eq!(Value::from(1.0), Value::from(1));
        assert_ne!(Value::from(1.0), Value::from(2));

        // 2 different, not comparable - big array to int
        assert_ne!(
            Value::from(vec![Value::from(1), Value::from(2)]),
            Value::from(1)
        );

        // object to array
        assert_ne!(
            Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap(),
            Value::from(vec![Value::from(1), Value::from(2)])
        );
    }

    #[test]
    fn test_arithmetic_op() {
        let a = Value::from(10);
        let b = Value::from(5.0);

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap(),
            Value::from(15)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Subtract).unwrap(),
            Value::from(5)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Multiply).unwrap(),
            Value::from(50)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Divide).unwrap(),
            Value::from(2)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Modulo).unwrap(),
            Value::from(0)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Exponentiate).unwrap(),
            Value::from(100000)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Negate).unwrap(),
            Value::from(-10)
        );
    }

    #[test]
    fn test_boolean_logic() {
        let a = Value::from(true);
        let b = Value::from(0);

        assert_eq!(
            Value::boolean_op(&a, &b, BooleanOperation::And).unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Value::boolean_op(&a, &b, BooleanOperation::Or).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Value::boolean_op(&a, &b, BooleanOperation::Not).unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Value::boolean_op(&a, &b, BooleanOperation::LT).unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Value::boolean_op(&a, &b, BooleanOperation::GT).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Value::boolean_op(&a, &b, BooleanOperation::LTE).unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Value::boolean_op(&a, &b, BooleanOperation::GTE).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Value::boolean_op(&a, &b, BooleanOperation::EQ).unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Value::boolean_op(&a, &b, BooleanOperation::NEQ).unwrap(),
            Value::from(true)
        );
    }

    #[test]
    fn test_indexing() {
        // Get index on array
        let array = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
        let v = array.get_index(&Value::from(1)).unwrap();
        assert_eq!(v, &Value::from(2));

        // Get index on object
        let object = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        let v = object.get_index(&Value::from("a")).unwrap();
        assert_eq!(v, &Value::from(1));

        // Get index on string
        Value::from("abc")
            .get_index(&Value::from(1))
            .expect_err("Expected error");

        // Get indices on array
        let array = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
        let v = array
            .get_indices(&Value::from(vec![Value::from(0), Value::from(1)]))
            .unwrap();
        assert_eq!(v, vec![&Value::from(1), &Value::from(2)]);

        // Get indices on object
        let object = Value::try_from(vec![
            (Value::from("a"), Value::from(1)),
            (Value::from("b"), Value::from(2)),
        ])
        .unwrap();
        let v = object
            .get_indices(&Value::from(vec![Value::from("a"), Value::from("b")]))
            .unwrap();
        assert_eq!(v, vec![&Value::from(1), &Value::from(2)]);

        // Get indices on int
        Value::from(1)
            .get_indices(&Value::from(vec![Value::from(0), Value::from(1)]))
            .expect_err("Expected error");

        // Get index_mut on array
        let mut array = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
        let v = array.get_index_mut(&Value::from(1)).unwrap();
        assert_eq!(v, &mut Value::from(2));

        // Get index_mut on object
        let mut object = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        let v = object.get_index_mut(&Value::from("a")).unwrap();
        assert_eq!(v, &mut Value::from(1));

        // Get index_mut on string
        Value::from("abc")
            .get_index_mut(&Value::from(1))
            .expect_err("Expected error");

        // Get indices_mut on array
        let mut array = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
        let v = array
            .get_indices_mut(&Value::from(vec![Value::from(0), Value::from(1)]))
            .unwrap();
        assert_eq!(v, vec![&mut Value::from(1), &mut Value::from(2)]);

        // Get indices_mut on object
        let mut object = Value::try_from(vec![
            (Value::from("a"), Value::from(1)),
            (Value::from("b"), Value::from(2)),
        ])
        .unwrap();
        let v = object
            .get_indices_mut(&Value::from(vec![Value::from("a"), Value::from("b")]))
            .unwrap();
        assert_eq!(v, vec![&mut Value::from(1), &mut Value::from(2)]);

        // Get indices_mut on int
        Value::from(1)
            .get_indices_mut(&Value::from(vec![Value::from(0), Value::from(1)]))
            .expect_err("Expected error");

        // Set index on array
        let mut array = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
        array.set_index(&Value::from(1), Value::from(4)).unwrap();
        assert_eq!(
            array,
            Value::from(vec![Value::from(1), Value::from(4), Value::from(3)])
        );

        // Set index on object
        let mut object = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        object.set_index(&Value::from("a"), Value::from(2)).unwrap();
        assert_eq!(
            object,
            Value::try_from(vec![(Value::from("a"), Value::from(2))]).unwrap()
        );

        // Set index on float
        Value::from(1)
            .set_index(&Value::from(1), Value::from(2))
            .expect_err("Expected error");
    }

    #[test]
    fn test_bitwise_op() {
        let l = Value::from(0b1010);
        let r = Value::from(0b1100);

        assert_eq!(
            Value::bitwise_op(&l, &r, BitwiseOperation::And).unwrap(),
            Value::from(0b1000)
        );

        assert_eq!(
            Value::bitwise_op(&l, &r, BitwiseOperation::Or).unwrap(),
            Value::from(0b1110)
        );

        assert_eq!(
            Value::bitwise_op(&l, &r, BitwiseOperation::Xor).unwrap(),
            Value::from(0b0110)
        );

        assert_eq!(
            Value::bitwise_op(&l, &Value::from(2), BitwiseOperation::LeftShift).unwrap(),
            Value::from(0b101000)
        );

        assert_eq!(
            Value::bitwise_op(&l, &Value::from(2), BitwiseOperation::RightShift).unwrap(),
            Value::from(0b10)
        );

        assert_eq!(
            Value::bitwise_op(&l, &r, BitwiseOperation::Not).unwrap(),
            Value::from(0b0101)
        );
    }
}
