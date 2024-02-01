//! This module defines the `Value` type, and the `ValueTrait` trait.
//! The `Value` type is an enum that can hold any of the supported value types.
//!
use std::str::FromStr;

use crate::operations::*;
use crate::tagged_value::TaggedValue;
use crate::types::*;
use crate::Error;
use crate::ValueType;
use serde::{Deserialize, Serialize};

/// A trait that all values must implement
/// It enforces a set of common traits and accessors
pub trait ValueTrait:
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
    /// The inner type of the value
    type Inner;

    /// Creates a new value from the given inner value
    fn new(inner: Self::Inner) -> Self;

    /// Returns a reference to the inner value
    fn inner(&self) -> &Self::Inner;

    /// Returns a mutable reference to the inner value
    fn inner_mut(&mut self) -> &mut Self::Inner;
}

/// Main value type
/// This is an enum that can hold any of the supported value types
#[derive(Clone, Serialize, Deserialize, Eq, Hash, PartialEq)]
#[serde(untagged)]
pub enum Value {
    /// A boolean value
    Bool(Bool),

    // The next 2 are up here for serialization purposes
    //
    /// An signed 64bit integer value
    I64(I64),

    /// A floating-point value
    Float(Float),

    /// An unsigned 8bit integer value
    U8(U8),

    /// An unsigned 8bit integer value
    I8(I8),

    /// An unsigned 16bit integer value
    U16(U16),

    /// An signed 16bit integer value
    I16(I16),

    /// An unsigned 32bit integer value
    U32(U32),

    /// An signed 32bit integer value
    I32(I32),

    /// An unsigned 64bit integer value
    U64(U64),

    /// A fixed-point value
    Fixed(Fixed),

    /// A currency value
    Currency(Currency),

    /// A string value
    String(Str),

    /// A range value
    /// This type will always resolve to array in all comparisons and operations
    Range(Range),

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
                if v.is_f64() {
                    Ok(Value::from(v.as_f64().unwrap()))
                } else {
                    Ok(Value::from(v.as_i64().unwrap()))
                }
            }
        }
    }
}

impl Value {
    /// Serializes the value to a tagged value
    /// This is useful for serialization, as it will preserve the type of integers
    pub fn serialize_tagged(&self) -> Result<String, serde_json::Error> {
        Ok(TaggedValue::from(self.clone()).serialize()?.to_string())
    }

    /// Deserializes a tagged value
    pub fn deserialize_tagged(value: &str) -> Result<Self, serde_json::Error> {
        TaggedValue::deserialize(&serde_json::Value::from_str(value)?).map(|x| x.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn bool(inner: impl Into<Bool>) -> Self {
        Value::Bool(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn u8(inner: impl Into<U8>) -> Self {
        Value::U8(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn i8(inner: impl Into<I8>) -> Self {
        Value::I8(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn u16(inner: impl Into<U16>) -> Self {
        Value::U16(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn i16(inner: impl Into<I16>) -> Self {
        Value::I16(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn u32(inner: impl Into<U32>) -> Self {
        Value::U32(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn i32(inner: impl Into<I32>) -> Self {
        Value::I32(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn u64(inner: impl Into<U64>) -> Self {
        Value::U64(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn i64(inner: impl Into<I64>) -> Self {
        Value::I64(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn float(inner: impl Into<Float>) -> Self {
        Value::Float(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn fixed(inner: impl Into<Fixed>) -> Self {
        Value::Fixed(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn currency(inner: impl Into<Currency>) -> Self {
        Value::Currency(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn string(inner: impl Into<Str>) -> Self {
        Value::String(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn range(inner: impl Into<Range>) -> Self {
        Value::Range(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn array(inner: impl Into<Array>) -> Self {
        Value::Array(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn object(inner: impl Into<Object>) -> Self {
        Value::Object(inner.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn int(inner: impl Into<I64>) -> Self {
        Value::I64(inner.into())
    }

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

            ValueType::U8 => (
                U8::try_from(self.clone())?.into(),
                U8::try_from(other.clone())?.into(),
            ),

            ValueType::U16 => (
                U16::try_from(self.clone())?.into(),
                U16::try_from(other.clone())?.into(),
            ),

            ValueType::U32 => (
                U32::try_from(self.clone())?.into(),
                U32::try_from(other.clone())?.into(),
            ),

            ValueType::U64 => (
                U64::try_from(self.clone())?.into(),
                U64::try_from(other.clone())?.into(),
            ),

            ValueType::I8 => (
                I8::try_from(self.clone())?.into(),
                I8::try_from(other.clone())?.into(),
            ),

            ValueType::I16 => (
                I16::try_from(self.clone())?.into(),
                I16::try_from(other.clone())?.into(),
            ),

            ValueType::I32 => (
                I32::try_from(self.clone())?.into(),
                I32::try_from(other.clone())?.into(),
            ),

            ValueType::I64 => (
                I64::try_from(self.clone())?.into(),
                I64::try_from(other.clone())?.into(),
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

            ValueType::Range => (
                Range::try_from(self.clone())?.into(),
                Range::try_from(other.clone())?.into(),
            ),

            ValueType::Int | ValueType::Numeric | ValueType::Compound | ValueType::Any => {
                unreachable!(
                    "Non-concrete type encountered in resolve: {:?}",
                    self.own_type()
                )
            }
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
            Value::U8(_) => ValueType::U8,
            Value::U16(_) => ValueType::U16,
            Value::U32(_) => ValueType::U32,
            Value::U64(_) => ValueType::U64,
            Value::I8(_) => ValueType::I8,
            Value::I16(_) => ValueType::I16,
            Value::I32(_) => ValueType::I32,
            Value::I64(_) => ValueType::I64,
            Value::String(_) => ValueType::String,
            Value::Range(_) => ValueType::Range,
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
    /// use polyvalue::types::I64;
    ///
    /// let value = Value::from(1.0);
    /// let int = value.as_a::<I64>().expect("Value could not be converted to int!");
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
        match (self.own_type(), type_name) {
            (_, ValueType::Any) => true,

            (
                ValueType::Array | ValueType::Object | ValueType::Range | ValueType::String,
                ValueType::Compound,
            ) => true,

            (
                ValueType::U8
                | ValueType::U16
                | ValueType::U32
                | ValueType::U64
                | ValueType::I8
                | ValueType::I16
                | ValueType::I32
                | ValueType::I64
                | ValueType::Fixed
                | ValueType::Float
                | ValueType::Currency,
                ValueType::Numeric,
            ) => true,

            (
                ValueType::U8
                | ValueType::U16
                | ValueType::U32
                | ValueType::U64
                | ValueType::I8
                | ValueType::I16
                | ValueType::I32
                | ValueType::I64,
                ValueType::Int,
            ) => true,

            (x, y) => x == y,
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
            ValueType::Fixed => Fixed::try_from(self.clone())?.into(),
            ValueType::Float => Float::try_from(self.clone())?.into(),
            ValueType::Currency => Currency::try_from(self.clone())?.into(),

            ValueType::U8 => U8::try_from(self.clone())?.into(),
            ValueType::U16 => U16::try_from(self.clone())?.into(),
            ValueType::U32 => U32::try_from(self.clone())?.into(),
            ValueType::U64 => U64::try_from(self.clone())?.into(),
            ValueType::I8 => I8::try_from(self.clone())?.into(),
            ValueType::I16 => I16::try_from(self.clone())?.into(),
            ValueType::I32 => I32::try_from(self.clone())?.into(),
            ValueType::I64 => I64::try_from(self.clone())?.into(),

            ValueType::String => Str::try_from(self.clone())?.into(),
            ValueType::Array => Array::try_from(self.clone())?.into(),
            ValueType::Object => Object::try_from(self.clone())?.into(),

            // Cannot convert to range
            ValueType::Range => {
                return Err(Error::ValueConversion {
                    src_type: self.own_type(),
                    dst_type: ValueType::Range,
                })
            }

            ValueType::Int => {
                if self.is_a(ValueType::Int) {
                    self.clone()
                } else {
                    I64::try_from(self.clone())?.into()
                }
            }

            ValueType::Compound => {
                if self.own_type() == ValueType::Array {
                    self.clone()
                } else {
                    Object::try_from(self.clone())?.into()
                }
            }

            ValueType::Numeric => {
                if self.is_a(ValueType::Numeric) {
                    self.clone()
                } else {
                    Fixed::try_from(self.clone())?.into()
                }
            }

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
            self.own_type()
        } else {
            match (self.own_type(), other.own_type()) {
                (ValueType::String, _) | (_, ValueType::String) => ValueType::String,
                (ValueType::Object, _) | (_, ValueType::Object) => ValueType::Object,
                (ValueType::Array, _) | (_, ValueType::Array) => ValueType::Array,
                (ValueType::Range, _) | (_, ValueType::Range) => ValueType::Range,

                (ValueType::Currency, _) | (_, ValueType::Currency) => ValueType::Currency,
                (ValueType::Fixed, _) | (_, ValueType::Fixed) => ValueType::Fixed,
                (ValueType::Float, _) | (_, ValueType::Float) => ValueType::Float,

                (ValueType::I64, _) | (_, ValueType::I64) => ValueType::I64,
                (ValueType::U64, _) | (_, ValueType::U64) => ValueType::U64,
                (ValueType::I32, _) | (_, ValueType::I32) => ValueType::I32,
                (ValueType::U32, _) | (_, ValueType::U32) => ValueType::U32,
                (ValueType::I16, _) | (_, ValueType::I16) => ValueType::I16,
                (ValueType::U16, _) | (_, ValueType::U16) => ValueType::U16,
                (ValueType::I8, _) | (_, ValueType::I8) => ValueType::I8,
                (ValueType::U8, _) | (_, ValueType::U8) => ValueType::U8,

                (ValueType::Bool, _)
                | (ValueType::Int, _)
                | (ValueType::Numeric, _)
                | (ValueType::Compound, _)
                | (ValueType::Any, _) => {
                    unreachable!(
                        "Non-concrete type encountered in resolve: {:?}",
                        self.own_type()
                    )
                }
            }
        }
    }

    /// Compares two values, ignoring type
    pub fn weak_equality(&self, other: &Self) -> Result<bool, Error> {
        let (l, r) = self.resolve(other)?;
        Ok(l == r)
    }

    /// Compares two values, ignoring type
    fn weak_ord(&self, other: &Self) -> Result<std::cmp::Ordering, Error> {
        let (l, r) = self.resolve(other)?;

        let res = match l.own_type() {
            ValueType::Bool => Bool::cmp(&l.as_a::<Bool>().unwrap(), &r.as_a::<Bool>().unwrap()),
            ValueType::Fixed => {
                Fixed::cmp(&l.as_a::<Fixed>().unwrap(), &r.as_a::<Fixed>().unwrap())
            }
            ValueType::Float => {
                Float::cmp(&l.as_a::<Float>().unwrap(), &r.as_a::<Float>().unwrap())
            }
            ValueType::Currency => Currency::cmp(
                &l.as_a::<Currency>().unwrap(),
                &r.as_a::<Currency>().unwrap(),
            ),

            ValueType::U8 => U8::cmp(&l.as_a::<U8>().unwrap(), &r.as_a::<U8>().unwrap()),
            ValueType::U16 => U16::cmp(&l.as_a::<U16>().unwrap(), &r.as_a::<U16>().unwrap()),
            ValueType::U32 => U32::cmp(&l.as_a::<U32>().unwrap(), &r.as_a::<U32>().unwrap()),
            ValueType::U64 => U64::cmp(&l.as_a::<U64>().unwrap(), &r.as_a::<U64>().unwrap()),

            ValueType::I8 => I8::cmp(&l.as_a::<I8>().unwrap(), &r.as_a::<I8>().unwrap()),
            ValueType::I16 => I16::cmp(&l.as_a::<I16>().unwrap(), &r.as_a::<I16>().unwrap()),
            ValueType::I32 => I32::cmp(&l.as_a::<I32>().unwrap(), &r.as_a::<I32>().unwrap()),
            ValueType::I64 => I64::cmp(&l.as_a::<I64>().unwrap(), &r.as_a::<I64>().unwrap()),

            ValueType::String => Str::cmp(&l.as_a::<Str>().unwrap(), &r.as_a::<Str>().unwrap()),
            ValueType::Range => {
                Range::cmp(&l.as_a::<Range>().unwrap(), &r.as_a::<Range>().unwrap())
            }
            ValueType::Array => {
                Array::cmp(&l.as_a::<Array>().unwrap(), &r.as_a::<Array>().unwrap())
            }
            ValueType::Object => {
                Object::cmp(&l.as_a::<Object>().unwrap(), &r.as_a::<Object>().unwrap())
            }

            ValueType::Int | ValueType::Numeric | ValueType::Compound | ValueType::Any => {
                unreachable!(
                    "Non-concrete type encountered in weak_ord: {:?}",
                    self.own_type()
                )
            }
        };

        Ok(res)
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(v) => write!(f, "{}", v),
            Value::Fixed(v) => write!(f, "{}", v),
            Value::Float(v) => write!(f, "{}", v),
            Value::Currency(v) => write!(f, "{}", v),

            Value::U8(v) => write!(f, "{}", v),
            Value::U16(v) => write!(f, "{}", v),
            Value::U32(v) => write!(f, "{}", v),
            Value::U64(v) => write!(f, "{}", v),

            Value::I8(v) => write!(f, "{}", v),
            Value::I16(v) => write!(f, "{}", v),
            Value::I32(v) => write!(f, "{}", v),
            Value::I64(v) => write!(f, "{}", v),

            Value::String(v) => write!(f, "{}", v),
            Value::Range(v) => write!(f, "{}", v),
            Value::Array(v) => write!(f, "{}", v),
            Value::Object(v) => write!(f, "{}", v),
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(v) => write!(f, "{:?}", v),
            Value::Fixed(v) => write!(f, "{:?}", v),
            Value::Float(v) => write!(f, "{:?}", v),
            Value::Currency(v) => write!(f, "{:?}", v),

            Value::U8(v) => write!(f, "{:?}", v),
            Value::U16(v) => write!(f, "{:?}", v),
            Value::U32(v) => write!(f, "{:?}", v),
            Value::U64(v) => write!(f, "{:?}", v),

            Value::I8(v) => write!(f, "{:?}", v),
            Value::I16(v) => write!(f, "{:?}", v),
            Value::I32(v) => write!(f, "{:?}", v),
            Value::I64(v) => write!(f, "{:?}", v),

            Value::String(v) => write!(f, "{:?}", v),
            Value::Range(v) => write!(f, "{:?}", v),
            Value::Array(v) => write!(f, "{:?}", v),
            Value::Object(v) => write!(f, "{:?}", v),
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let weak_order = self.weak_ord(other).ok()?;
        if weak_order == std::cmp::Ordering::Equal && self.own_type() != other.own_type() {
            match (self, other) {
                (Value::Bool(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::Bool(_)) => Some(std::cmp::Ordering::Greater),

                (Value::U8(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::U8(_)) => Some(std::cmp::Ordering::Greater),

                (Value::I8(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::I8(_)) => Some(std::cmp::Ordering::Greater),

                (Value::U16(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::U16(_)) => Some(std::cmp::Ordering::Greater),

                (Value::I16(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::I16(_)) => Some(std::cmp::Ordering::Greater),

                (Value::U32(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::U32(_)) => Some(std::cmp::Ordering::Greater),

                (Value::I32(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::I32(_)) => Some(std::cmp::Ordering::Greater),

                (Value::U64(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::U64(_)) => Some(std::cmp::Ordering::Greater),

                (Value::I64(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::I64(_)) => Some(std::cmp::Ordering::Greater),

                (Value::Float(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::Float(_)) => Some(std::cmp::Ordering::Greater),

                (Value::Fixed(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::Fixed(_)) => Some(std::cmp::Ordering::Greater),

                (Value::Currency(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::Currency(_)) => Some(std::cmp::Ordering::Greater),

                (Value::String(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::String(_)) => Some(std::cmp::Ordering::Greater),

                (Value::Range(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::Range(_)) => Some(std::cmp::Ordering::Greater),

                (Value::Array(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::Array(_)) => Some(std::cmp::Ordering::Greater),

                _ => unreachable!("This covers Object <-> Object, which is not possible here"),
            }
        } else {
            Some(weak_order)
        }
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if let Some(ordering) = self.partial_cmp(other) {
            ordering
        } else {
            // Ranges-other will always be a weak-comparison
            match (self.own_type(), other.own_type()) {
                (ValueType::Range, _) => std::cmp::Ordering::Greater,
                (_, ValueType::Range) => std::cmp::Ordering::Less,

                // We should in theory never get here
                // Anything here is a bug in resolution order logic
                _ => unreachable!("Could not compare values {:?} and {:?}", self, other),
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

            (Value::U8(l), Value::U8(r)) => U8::boolean_op(&l, &r, operation).map(Into::into),
            (Value::U16(l), Value::U16(r)) => U16::boolean_op(&l, &r, operation).map(Into::into),
            (Value::U32(l), Value::U32(r)) => U32::boolean_op(&l, &r, operation).map(Into::into),
            (Value::U64(l), Value::U64(r)) => U64::boolean_op(&l, &r, operation).map(Into::into),
            (Value::I8(l), Value::I8(r)) => I8::boolean_op(&l, &r, operation).map(Into::into),
            (Value::I16(l), Value::I16(r)) => I16::boolean_op(&l, &r, operation).map(Into::into),
            (Value::I32(l), Value::I32(r)) => I32::boolean_op(&l, &r, operation).map(Into::into),
            (Value::I64(l), Value::I64(r)) => I64::boolean_op(&l, &r, operation).map(Into::into),

            (Value::String(l), Value::String(r)) => {
                Str::boolean_op(&l, &r, operation).map(Into::into)
            }
            (Value::Array(l), Value::Array(r)) => {
                Array::boolean_op(&l, &r, operation).map(Into::into)
            }
            (Value::Object(l), Value::Object(r)) => {
                Object::boolean_op(&l, &r, operation).map(Into::into)
            }
            (Value::Range(l), Value::Range(r)) => {
                Range::boolean_op(&l, &r, operation).map(Into::into)
            }

            _ => unreachable!("Invalid type combination for boolean operation"),
        }
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Self::boolean_op(self, &self.clone(), BooleanOperation::Not)
    }
}

impl BitwiseOperationExt for Value {
    fn bitwise_op(left: &Self, right: &Self, operation: BitwiseOperation) -> Result<Self, Error> {
        let (left, right) = left.resolve(right)?;
        match (&left, &right) {
            (Value::U8(l), Value::U8(r)) => U8::bitwise_op(&l, &r, operation).map(Into::into),
            (Value::U16(l), Value::U16(r)) => U16::bitwise_op(&l, &r, operation).map(Into::into),
            (Value::U32(l), Value::U32(r)) => U32::bitwise_op(&l, &r, operation).map(Into::into),
            (Value::U64(l), Value::U64(r)) => U64::bitwise_op(&l, &r, operation).map(Into::into),
            (Value::I8(l), Value::I8(r)) => I8::bitwise_op(&l, &r, operation).map(Into::into),
            (Value::I16(l), Value::I16(r)) => I16::bitwise_op(&l, &r, operation).map(Into::into),
            (Value::I32(l), Value::I32(r)) => I32::bitwise_op(&l, &r, operation).map(Into::into),

            _ => {
                let left = left.as_a::<I64>()?;
                let right = right.as_a::<I64>()?;
                I64::bitwise_op(&left, &right, operation).map(Into::into)
            }
        }
    }

    fn bitwise_not(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Self::bitwise_op(self, &self.clone(), BitwiseOperation::Not)
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

            (Value::U8(l), Value::U8(r)) => U8::arithmetic_op(&l, &r, operation).map(Into::into),
            (Value::U16(l), Value::U16(r)) => U16::arithmetic_op(&l, &r, operation).map(Into::into),
            (Value::U32(l), Value::U32(r)) => U32::arithmetic_op(&l, &r, operation).map(Into::into),
            (Value::U64(l), Value::U64(r)) => U64::arithmetic_op(&l, &r, operation).map(Into::into),
            (Value::I8(l), Value::I8(r)) => I8::arithmetic_op(&l, &r, operation).map(Into::into),
            (Value::I16(l), Value::I16(r)) => I16::arithmetic_op(&l, &r, operation).map(Into::into),
            (Value::I32(l), Value::I32(r)) => I32::arithmetic_op(&l, &r, operation).map(Into::into),
            (Value::I64(l), Value::I64(r)) => I64::arithmetic_op(&l, &r, operation).map(Into::into),

            (Value::String(l), Value::String(r)) => {
                Str::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            (Value::Array(l), Value::Array(r)) => {
                Array::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            (Value::Object(l), Value::Object(r)) => {
                Object::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            (Value::Range(l), Value::Range(r)) => {
                Range::arithmetic_op(&l, &r, operation).map(Into::into)
            }
            _ => unreachable!("Invalid type combination during boolean operation"),
        }
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Self::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }

    fn is_operator_supported(&self, other: &Self, operation: ArithmeticOperation) -> bool {
        match self.type_for_comparison(other) {
            ValueType::Bool => Bool::is_operator_supported(
                &self.as_a::<Bool>().unwrap(),
                &other.as_a::<Bool>().unwrap(),
                operation,
            ),
            ValueType::Fixed => Fixed::is_operator_supported(
                &self.as_a::<Fixed>().unwrap(),
                &other.as_a::<Fixed>().unwrap(),
                operation,
            ),
            ValueType::Float => Float::is_operator_supported(
                &self.as_a::<Float>().unwrap(),
                &other.as_a::<Float>().unwrap(),
                operation,
            ),
            ValueType::Currency => Currency::is_operator_supported(
                &self.as_a::<Currency>().unwrap(),
                &other.as_a::<Currency>().unwrap(),
                operation,
            ),
            ValueType::U8 => U8::is_operator_supported(
                &self.as_a::<U8>().unwrap(),
                &other.as_a::<U8>().unwrap(),
                operation,
            ),
            ValueType::U16 => U16::is_operator_supported(
                &self.as_a::<U16>().unwrap(),
                &other.as_a::<U16>().unwrap(),
                operation,
            ),
            ValueType::U32 => U32::is_operator_supported(
                &self.as_a::<U32>().unwrap(),
                &other.as_a::<U32>().unwrap(),
                operation,
            ),
            ValueType::U64 => U64::is_operator_supported(
                &self.as_a::<U64>().unwrap(),
                &other.as_a::<U64>().unwrap(),
                operation,
            ),
            ValueType::I8 => I8::is_operator_supported(
                &self.as_a::<I8>().unwrap(),
                &other.as_a::<I8>().unwrap(),
                operation,
            ),
            ValueType::I16 => I16::is_operator_supported(
                &self.as_a::<I16>().unwrap(),
                &other.as_a::<I16>().unwrap(),
                operation,
            ),
            ValueType::I32 => I32::is_operator_supported(
                &self.as_a::<I32>().unwrap(),
                &other.as_a::<I32>().unwrap(),
                operation,
            ),
            ValueType::I64 => I64::is_operator_supported(
                &self.as_a::<I64>().unwrap(),
                &other.as_a::<I64>().unwrap(),
                operation,
            ),
            ValueType::String => Str::is_operator_supported(
                &self.as_a::<Str>().unwrap(),
                &other.as_a::<Str>().unwrap(),
                operation,
            ),
            ValueType::Array => Array::is_operator_supported(
                &self.as_a::<Array>().unwrap(),
                &other.as_a::<Array>().unwrap(),
                operation,
            ),
            ValueType::Object => Object::is_operator_supported(
                &self.as_a::<Object>().unwrap(),
                &other.as_a::<Object>().unwrap(),
                operation,
            ),
            ValueType::Range => Range::is_operator_supported(
                &self.as_a::<Range>().unwrap(),
                &other.as_a::<Range>().unwrap(),
                operation,
            ),

            ValueType::Int | ValueType::Numeric | ValueType::Compound | ValueType::Any => {
                unreachable!(
                    "Non-concrete type encountered in is_operator_supported: {:?}",
                    self.own_type()
                )
            }
        }
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
        } else {
            match container.own_type() {
                ValueType::Array => {
                    return Array::matching_op(&container.as_a::<Array>()?, pattern, operation)
                }

                ValueType::Object => {
                    return Object::matching_op(&container.as_a::<Object>()?, pattern, operation)
                }

                ValueType::Range => {
                    return Range::matching_op(&container.as_a::<Range>()?, pattern, operation)
                }

                _ => Str::matching_op(&container.as_a::<Str>()?, pattern, operation),
            }
        }
    }
}

impl IndexingOperationExt for Value {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        match self {
            Value::Array(v) => v.get_index(index),
            Value::Object(v) => v.get_index(index),
            Value::Range(v) => v.get_index(index),
            Value::String(v) => v.get_index(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }

    fn get_indices(&self, index: &Value) -> Result<Value, crate::Error> {
        match self {
            Value::Array(v) => v.get_indices(index),
            Value::Object(v) => v.get_indices(index),
            Value::Range(v) => v.get_indices(index),
            Value::String(v) => v.get_indices(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Compound,
            })?,
        }
    }
}

impl IndexingMutationExt for Value {
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
    use fpdec::{Dec, Decimal};
    use std::{cmp::Ordering, vec};

    #[test]
    fn test_tagged_serialization() {
        let value = Value::from(1.0);
        let serialized = serde_json::to_string(&value).unwrap();
        assert_eq!(serialized, "1.0");
        let deserialized: Value = serde_json::from_str(&serialized).unwrap();
        assert_eq!(value, deserialized);

        let serialized = value.serialize_tagged().unwrap();
        assert_eq!(serialized, r#"{"Float":1.0}"#);
        let deserialized: Value = Value::deserialize_tagged(&serialized).unwrap();
        assert_eq!(value, deserialized);
    }

    #[test]
    fn test_constructors() {
        macro_rules! assert_matches_type {
            ($value:expr, $type:ident) => {
                assert_eq!($value.own_type(), ValueType::$type);
            };
        }

        assert_matches_type!(Value::bool(true), Bool);
        assert_matches_type!(Value::u8(1), U8);
        assert_matches_type!(Value::u16(1), U16);
        assert_matches_type!(Value::u32(1), U32);
        assert_matches_type!(Value::u64(1), U64);
        assert_matches_type!(Value::i8(1), I8);
        assert_matches_type!(Value::i16(1), I16);
        assert_matches_type!(Value::i32(1), I32);
        assert_matches_type!(Value::i64(1), I64);
        assert_matches_type!(Value::float(1.0), Float);
        assert_matches_type!(Value::fixed(Dec!(1.0)), Fixed);
        assert_matches_type!(Value::currency(Dec!(1.0)), Currency);
        assert_matches_type!(Value::string("abc"), String);
        assert_matches_type!(Value::range(1..=2), Range);
        assert_matches_type!(Value::array(vec![Value::i64(1)]), Array);
        assert_matches_type!(
            Value::object(ObjectInner::try_from(vec![(Value::from("a"), Value::i64(1))]).unwrap()),
            Object
        );

        assert_matches_type!(Value::int(1), I64);
    }

    #[test]
    fn test_from_json_value() {
        let value = serde_json::json!({
            "bool": true,
            "fixed": 1.0,
            "float": 1.0,
            "currency": 1.0,
            "int": 1,
            "string": "abc",
            "array": [1, 2, 3],
            "object": {"a": 1},
            "range": [1, 2, 3],
            "null": serde_json::Value::Null,
        });
        let value = Value::try_from(value).unwrap();
        assert_eq!(value.own_type(), ValueType::Object);
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("bool")),
            Some(&Value::from(true))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("fixed")),
            Some(&Value::from(1.0))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("float")),
            Some(&Value::from(1.0))
        );
        assert_eq!(
            value
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("currency")),
            Some(&Value::from(1.0))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("int")),
            Some(&Value::from(1i64))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("string")),
            Some(&Value::from("abc"))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("array")),
            Some(&Value::from(vec![
                Value::i64(1),
                Value::i64(2),
                Value::i64(3)
            ]))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("range")),
            Some(&Value::from(vec![
                Value::i64(1),
                Value::i64(2),
                Value::i64(3)
            ]))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("null")),
            Some(&Value::from(""))
        );
    }

    #[test]
    fn test_matching() {
        let value = Value::from(1.0);
        let pattern = Value::from("float");
        let result = Value::matching_op(&value, &pattern, MatchingOperation::Is)
            .expect("Could not perform matching operation");
        assert_eq!(result, Value::from(true));

        let value = Value::from(vec![Value::from(1.0)]);
        let pattern = Value::from(Value::from(1.0));
        let result = Value::matching_op(&value, &pattern, MatchingOperation::Contains).unwrap();
        assert_eq!(result, Value::from(true));

        let value = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        let pattern = Value::from(Value::from("a"));
        let result = Value::matching_op(&value, &pattern, MatchingOperation::Contains).unwrap();
        assert_eq!(result, Value::from(true));

        let value = Value::from(Range::from(1..=2));
        let pattern = Value::from(Value::from(1));
        let result = Value::matching_op(&value, &pattern, MatchingOperation::Contains).unwrap();
        assert_eq!(result, Value::from(true));

        let value = Value::from("test");
        let pattern = Value::from("test");
        let result = Value::matching_op(&value, &pattern, MatchingOperation::Matches).unwrap();
        assert_eq!(result, Value::from(true));
    }

    #[test]
    fn test_resolve() {
        let a = Value::from(1.0);
        let b = Value::from(2);
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Float);
        assert!(b.own_type() == ValueType::Float);

        let a = Value::from(Fixed::zero());
        let b = Value::from(2);
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Fixed);
        assert!(b.own_type() == ValueType::Fixed);

        let a = Value::from(false);
        let b = Value::from(true);
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Bool);
        assert!(b.own_type() == ValueType::Bool);

        let a = Value::from(1);
        let b = Value::from(2);
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::I32);
        assert!(b.own_type() == ValueType::I32);

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

        let a = Value::from(CurrencyInner::as_dollars(Fixed::from(Fixed::zero())));
        let b = Value::from(Fixed::from(Fixed::zero()));
        let (a, b) = a.resolve(&b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Currency);
        assert!(b.own_type() == ValueType::Currency);
    }

    #[test]
    fn test_own_type() {
        assert_eq!(Value::from(false).own_type(), ValueType::Bool);
        assert_eq!(Value::from(1.0).own_type(), ValueType::Float);
        assert_eq!(Value::from(1).own_type(), ValueType::I32);
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
            Value::from(CurrencyInner::as_dollars(Fixed::from(Fixed::zero()))).own_type(),
            ValueType::Currency
        );

        assert_eq!(
            Value::from(Fixed::from(Fixed::zero())).own_type(),
            ValueType::Fixed
        );

        assert_eq!(Value::from(Range::from(1..=2)).own_type(), ValueType::Range);
    }

    #[test]
    fn test_either_type() {
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
            .as_a::<I64>()
            .expect("Value could not be converted to int!");
        assert_eq!(int, I64::from(1i64));

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
            Object::try_from(vec![(Value::u64(0), Value::from(1.0))]).unwrap()
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

        assert!(Value::from(1).is_a(ValueType::Numeric));
        assert!(Value::from(1).is_a(ValueType::Any));

        assert!(Value::from(1.0).is_a(ValueType::Numeric));
        assert!(Value::from(Fixed::zero()).is_a(ValueType::Numeric));
        assert!(
            Value::from(CurrencyInner::as_dollars(Fixed::from(Fixed::zero())))
                .is_a(ValueType::Numeric)
        );
        assert!(Value::from(1u8).is_a(ValueType::Numeric));
        assert!(Value::from(1u16).is_a(ValueType::Numeric));
        assert!(Value::from(1u32).is_a(ValueType::Numeric));
        assert!(Value::from(1u64).is_a(ValueType::Numeric));
        assert!(Value::from(1i8).is_a(ValueType::Numeric));
        assert!(Value::from(1i16).is_a(ValueType::Numeric));
        assert!(Value::from(I32::new(1)).is_a(ValueType::Numeric));
        assert!(Value::from(I64::new(1)).is_a(ValueType::Numeric));
    }

    #[test]
    fn test_as_type() {
        let value = Value::from(1).as_type(ValueType::Int).unwrap();
        assert_eq!(value, Value::from(1));

        let value = Value::from(Fixed::one())
            .as_type(ValueType::Numeric)
            .unwrap();
        assert_eq!(value, Value::from(Fixed::one()));

        Value::from("a").as_type(ValueType::Numeric).unwrap_err();

        let value = Value::from(1.0);
        let int = value
            .as_type(ValueType::Int)
            .expect("Value could not be converted to int!");
        assert_eq!(int, Value::i64(1));

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
            Value::try_from(vec![(Value::u64(0), Value::from(1.0))]).unwrap()
        );

        let value = Value::from(1.0);
        let value = value
            .as_type(ValueType::Any)
            .expect("Value could not be converted to any!");
        assert_eq!(value, Value::from(1.0));

        let value = Value::from(1);
        assert_eq!(value.as_type(ValueType::Numeric).unwrap(), Value::i32(1));

        let value = Value::from(1.0);
        assert_eq!(value.as_type(ValueType::Numeric).unwrap(), Value::from(1.0));

        let value = Value::from(CurrencyInner::as_dollars(Fixed::from(Fixed::zero())));
        assert_eq!(
            value.as_type(ValueType::Numeric).unwrap(),
            Value::from(CurrencyInner::as_dollars(Fixed::from(Fixed::zero())))
        );

        let value = Value::from(Fixed::zero());
        assert_eq!(
            value.as_type(ValueType::Numeric).unwrap(),
            Value::from(Fixed::from(Fixed::zero()))
        );

        assert_eq!(
            Value::from(1).as_type(ValueType::Bool).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Value::from(0).as_type(ValueType::Fixed).unwrap(),
            Value::from(Fixed::from(Fixed::zero()))
        );

        assert_eq!(
            Value::from(0).as_type(ValueType::Currency).unwrap(),
            Value::from(CurrencyInner::from_fixed(Fixed::from(Fixed::zero())))
        );

        assert_eq!(
            Value::from(1).as_type(ValueType::String).unwrap(),
            Value::from("1")
        );

        assert_eq!(
            Value::from(1).as_type(ValueType::Array).unwrap(),
            Value::from(vec![Value::from(1)])
        );

        assert_eq!(
            Value::from(1).as_type(ValueType::Object).unwrap(),
            Value::try_from(vec![(Value::u64(0), Value::from(1))]).unwrap()
        );

        // u8 etc
        assert_eq!(
            Value::from(1).as_type(ValueType::U8).unwrap(),
            Value::from(1u8)
        );
        assert_eq!(
            Value::from(1).as_type(ValueType::U16).unwrap(),
            Value::from(1u16)
        );
        assert_eq!(
            Value::from(1).as_type(ValueType::U32).unwrap(),
            Value::from(1u32)
        );
        assert_eq!(
            Value::from(1).as_type(ValueType::U64).unwrap(),
            Value::from(1u64)
        );
        assert_eq!(
            Value::from(1).as_type(ValueType::I8).unwrap(),
            Value::from(1i8)
        );
        assert_eq!(
            Value::from(1).as_type(ValueType::I16).unwrap(),
            Value::from(1i16)
        );
        assert_eq!(
            Value::from(1).as_type(ValueType::I32).unwrap(),
            Value::from(I32::new(1))
        );
        assert_eq!(
            Value::from(1).as_type(ValueType::I64).unwrap(),
            Value::from(I64::new(1))
        );

        Value::from(vec![Value::from(1)])
            .as_type(ValueType::Compound)
            .unwrap();

        Value::from(1).as_type(ValueType::Range).unwrap_err();

        let u = u8::try_from(1i64);
        assert!(u.is_ok());
    }

    #[test]
    fn test_type_for_comparison() {
        macro_rules! assert_type_for_comparison {
            ($a:expr, $b:expr, $expected:expr) => {
                assert_eq!(
                    Value::from($a).type_for_comparison(&Value::from($b)),
                    $expected,
                    "Expected {:?} to be {:?}",
                    Value::from($a),
                    $expected
                );
            };
        }

        assert_type_for_comparison!(true, false, ValueType::Bool);
        assert_type_for_comparison!(1.0, 2, ValueType::Float);

        assert_type_for_comparison!(1i64, true, ValueType::I64);
        assert_type_for_comparison!(1, "abc", ValueType::String);
        assert_type_for_comparison!(1, vec![Value::from(1)], ValueType::Array);

        assert_type_for_comparison!(
            vec![Value::from(1)],
            ObjectInner::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap(),
            ValueType::Object
        );

        assert_type_for_comparison!(
            1,
            CurrencyInner::as_dollars(Fixed::from(Fixed::zero())),
            ValueType::Currency
        );

        assert_type_for_comparison!(
            CurrencyInner::as_dollars(Fixed::from(Fixed::zero())),
            Fixed::from(Fixed::zero()),
            ValueType::Currency
        );

        assert_type_for_comparison!(1u8, 1u16, ValueType::U16);
        assert_type_for_comparison!(1u8, 1u32, ValueType::U32);
        assert_type_for_comparison!(1u8, 1u64, ValueType::U64);
        assert_type_for_comparison!(1u8, 1i8, ValueType::I8);
        assert_type_for_comparison!(1u8, 1i16, ValueType::I16);
        assert_type_for_comparison!(1u8, I32::new(1), ValueType::I32);
        assert_type_for_comparison!(1u8, I64::new(1), ValueType::I64);
        assert_type_for_comparison!(1u8, true, ValueType::U8);
        assert_type_for_comparison!(true, false, ValueType::Bool);
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
            Value::from(CurrencyInner::as_dollars(Fixed::from(Fixed::zero()))).to_string(),
            "$0.00"
        );

        assert_eq!(Value::from(1u8).to_string(), "1");
        assert_eq!(Value::from(1u16).to_string(), "1");
        assert_eq!(Value::from(1u32).to_string(), "1");
        assert_eq!(Value::from(1u64).to_string(), "1");
        assert_eq!(Value::from(1i8).to_string(), "1");
        assert_eq!(Value::from(1i16).to_string(), "1");
        assert_eq!(Value::from(I32::new(1)).to_string(), "1");
        assert_eq!(Value::from(I64::new(1)).to_string(), "1");
    }

    #[test]
    fn test_ord() {
        /*
         * We test all possible combinations of types
         * and make sure that the ordering is correct
         * We do not need to test all possible values
         * as the underlying types should test those
         */

        /// Asserts than left > right
        /// and right < left
        /// and right == right
        /// and left == left
        /// Usage:
        /// assert_ord!(true, 1u8);
        macro_rules! assert_ord {
            ($least:expr, $most:expr) => {
                assert_eq!(
                    Value::from($least).cmp(&Value::from($most)),
                    Ordering::Less,
                    "Expected {:?} < {:?}",
                    $least,
                    $most
                );
                assert_eq!(
                    Value::from($most).cmp(&Value::from($least)),
                    Ordering::Greater,
                    "Expected {:?} > {:?}",
                    $most,
                    $least
                );
                assert_eq!(
                    Value::from($most).cmp(&Value::from($most)),
                    Ordering::Equal,
                    "Expected {:?} == {:?}",
                    $most,
                    $most
                );
                assert_eq!(
                    Value::from($least).cmp(&Value::from($least)),
                    Ordering::Equal,
                    "Expected {:?} == {:?}",
                    $least,
                    $least
                );
            };
        }

        assert_ord!(true, 1u8);

        assert_ord!(1u8, 1i8);
        assert_ord!(1i8, 1u16);
        assert_ord!(1u16, 1i16);
        assert_ord!(1i16, 1u32);
        assert_ord!(1u32, 1i32);
        assert_ord!(1i32, 1u64);
        assert_ord!(1u64, 1i64);
        assert_ord!(1i64, 1f64);

        assert_ord!(1f64, Fixed::one());
        assert_ord!(Fixed::one(), CurrencyInner::as_dollars(Fixed::one()));
        assert_ord!(CurrencyInner::as_dollars(Fixed::one()), "$1.00");

        assert_ord!("1..2", 1..=2);
        assert_ord!(1..=2, vec![Value::from(1i64), Value::from(2i64)]);

        assert_ord!(
            vec![Value::from(1), Value::from(2)],
            ObjectInner::try_from(vec![(0i64.into(), 1.into()), (1i64.into(), 2.into())]).unwrap()
        );

        assert_ord!(
            1..=2,
            ObjectInner::try_from(vec![(0i64.into(), 1i64.into()), (1i64.into(), 2i64.into())])
                .unwrap()
        );

        assert_ord!(1, 1..=2);
    }

    #[test]
    fn test_eq() {
        // 2 of the same - string to string
        assert_eq!(Value::from("abc"), Value::from("abc"));
        assert_ne!(Value::from("cba"), Value::from("abc"));

        // 2 different, but comparable - float to int
        assert_ne!(Value::from(1.0), Value::from(1));
        assert_eq!(
            Value::from(1.0).weak_equality(&Value::from(1)).unwrap(),
            true
        );

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

        // range to int
        assert_ne!(Value::from(1..=2), Value::from(1));
        assert_eq!(Value::from(1..=2).cmp(&Value::from(1)), Ordering::Greater);
        assert_eq!(Value::from(1).cmp(&Value::from(1..=2)), Ordering::Less);
    }

    #[test]
    fn test_arithmetic_op() {
        let a = Value::from(10);
        let b = Value::from(5.0);

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap(),
            Value::from(15.0)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Subtract).unwrap(),
            Value::from(5.0)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Multiply).unwrap(),
            Value::from(50.0)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Divide).unwrap(),
            Value::from(2.0)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Modulo).unwrap(),
            Value::from(0.0)
        );

        assert_eq!(
            Value::arithmetic_op(&a, &b, ArithmeticOperation::Exponentiate).unwrap(),
            Value::from(100000.0)
        );

        assert_eq!(Value::arithmetic_neg(&a).unwrap(), Value::from(-10));

        Value::arithmetic_neg(&Value::from("test")).unwrap();
        Value::arithmetic_neg(&Value::from(false)).unwrap();
        Value::arithmetic_neg(&Value::from(1)).unwrap();
        Value::arithmetic_neg(&Value::from(1.0)).unwrap();
        Value::arithmetic_neg(&Value::from(Fixed::zero())).unwrap();
        Value::arithmetic_neg(&Value::from(CurrencyInner::as_dollars(Fixed::from(
            Fixed::zero(),
        ))))
        .unwrap();
        Value::arithmetic_op(
            &Value::from(1u8),
            &Value::from(1u8),
            ArithmeticOperation::Add,
        )
        .unwrap();
        Value::arithmetic_op(
            &Value::from(1u16),
            &Value::from(1u8),
            ArithmeticOperation::Add,
        )
        .unwrap();
        Value::arithmetic_op(
            &Value::from(1u32),
            &Value::from(1u8),
            ArithmeticOperation::Add,
        )
        .unwrap();
        Value::arithmetic_op(
            &Value::from(1u64),
            &Value::from(1u8),
            ArithmeticOperation::Add,
        )
        .unwrap();

        Value::arithmetic_neg(&Value::from(1i8)).unwrap();
        Value::arithmetic_neg(&Value::from(1i16)).unwrap();
        Value::arithmetic_neg(&Value::from(I32::new(1))).unwrap();
        Value::arithmetic_neg(&Value::from(I64::new(1))).unwrap();

        let a = Value::from(vec![Value::from(1), Value::from(2)]);
        let b = Value::from(vec![Value::from(3), Value::from(4)]);
        Value::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap();

        let a = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        let b = Value::try_from(vec![(Value::from("b"), Value::from(2))]).unwrap();
        Value::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap();

        let a = Value::from(1..=2);
        let b = Value::from(3..=4);
        Value::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap_err();

        assert_eq!(
            true,
            Value::from(false).is_operator_supported(&Value::from(false), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from("false")
                .is_operator_supported(&Value::from(false), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(1u8).is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(1i8).is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(1u16).is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(1i16).is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(1u32).is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(I32::new(1))
                .is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(I64::new(1))
                .is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(1u64).is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(1).is_operator_supported(&Value::from(1), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(1.0).is_operator_supported(&Value::from(1.0), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(Fixed::zero())
                .is_operator_supported(&Value::from(Fixed::zero()), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(CurrencyInner::as_dollars(Fixed::from(Fixed::zero())))
                .is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            false,
            Value::from(0..=10)
                .is_operator_supported(&Value::from(0..=10), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(vec![Value::from(1)])
                .is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::try_from(vec![(Value::from("a"), Value::from(1))])
                .unwrap()
                .is_operator_supported(&Value::from(1u8), ArithmeticOperation::Add)
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

        assert_eq!(Value::boolean_not(&a).unwrap(), Value::from(false));

        // fixed, float, and currency - boolean_not
        let a = Value::from(1.0);
        assert_eq!(Value::boolean_not(&a).unwrap(), Value::from(false));
        let a = Value::from(Fixed::zero());
        assert_eq!(Value::boolean_not(&a).unwrap(), Value::from(true));
        let a = Value::from(CurrencyInner::as_dollars(Fixed::from(Fixed::zero())));
        assert_eq!(Value::boolean_not(&a).unwrap(), Value::from(true));

        // string, array, object, range - boolean_not
        let a = Value::from("abc");
        assert_eq!(Value::boolean_not(&a).unwrap(), Value::from(false));
        let a = Value::from(vec![Value::from(1)]);
        assert_eq!(Value::boolean_not(&a).unwrap(), Value::from(false));
        let a = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        assert_eq!(Value::boolean_not(&a).unwrap(), Value::from(false));
        let a = Value::from(1..=2);
        assert_eq!(Value::boolean_not(&a).unwrap(), Value::from(false));

        // u8, i8, u16, i16, u32, i32, u64, i64 - boolean_not
        assert_eq!(
            Value::boolean_not(&Value::from(1u8)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(&Value::from(1i8)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(&Value::from(1u16)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(&Value::from(1i16)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(&Value::from(1u32)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(&Value::from(I32::new(1))).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(&Value::from(I64::new(1))).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(&Value::from(1u64)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(&Value::from(1i64)).unwrap(),
            Value::from(false)
        );
    }

    #[test]
    fn test_indexing() {
        // Get index on array
        let array = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
        let v = array.get_index(&Value::from(1)).unwrap();
        assert_eq!(v, Value::from(2));

        // Get index on object
        let object = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        let v = object.get_index(&Value::from("a")).unwrap();
        assert_eq!(v, Value::from(1));

        // Get index on string
        assert_eq!(
            Value::from("abc").get_index(&Value::from(1)).unwrap(),
            Value::from("b")
        );

        Value::from(1.0).get_index(&Value::from(1)).unwrap_err();

        // Get indices on array
        let array = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
        let v = array
            .get_indices(&Value::from(vec![Value::from(0), Value::from(1)]))
            .unwrap();
        assert_eq!(v, Value::from(vec![Value::from(1), Value::from(2)]));

        // Get indices on object
        let object = Value::try_from(vec![
            (Value::from("a"), Value::from(1)),
            (Value::from("b"), Value::from(2)),
        ])
        .unwrap();
        let v = object
            .get_indices(&Value::from(vec![Value::from("a"), Value::from("b")]))
            .unwrap();
        assert_eq!(v, Value::from(vec![Value::from(1), Value::from(2)]));

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
        assert!(v.contains(&&mut Value::from(1)));
        assert!(v.contains(&&mut Value::from(2)));

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

        // Delete index on array
        let mut array = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
        let v = array.delete_index(&Value::from(1)).unwrap();
        assert_eq!(v, Value::from(2));

        // Delete index on object
        let mut object = Value::try_from(vec![
            (Value::from("a"), Value::from(1)),
            (Value::from("b"), Value::from(2)),
        ])
        .unwrap();
        let v = object.delete_index(&Value::from("a")).unwrap();
        assert_eq!(v, Value::from(1));

        // Delete index on float
        Value::from(1.0)
            .delete_index(&Value::from(1))
            .expect_err("Expected error");

        // Get index on range
        let range = Value::from(Range::from(1..=3));
        let v = range.get_index(&Value::from(1)).unwrap();
        assert_eq!(v, Value::from(2i64));

        // Get indices on range
        let range = Value::from(Range::from(1..=3));
        let v = range
            .get_indices(&Value::from(vec![Value::from(0), Value::from(1)]))
            .unwrap();
        assert_eq!(v, Value::from(vec![Value::from(1i64), Value::from(2i64)]));

        // Get indices on string
        assert_eq!(
            Value::from("abc")
                .get_indices(&Value::from(vec![Value::from(0), Value::from(1)]))
                .unwrap(),
            Value::from("ab")
        );
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
            Value::bitwise_op(&l, &Value::from(-2), BitwiseOperation::LeftShift).unwrap(),
            Value::from(2)
        );

        assert_eq!(
            Value::bitwise_op(&l, &Value::from(2000), BitwiseOperation::LeftShift).unwrap(),
            Value::from(655360)
        );

        assert_eq!(
            Value::bitwise_op(&l, &Value::from(2), BitwiseOperation::RightShift).unwrap(),
            Value::from(0b10)
        );

        assert_eq!(
            Value::bitwise_op(&l, &Value::from(-1), BitwiseOperation::RightShift).unwrap(),
            Value::from(20)
        );

        assert_eq!(
            Value::bitwise_op(&l, &Value::from(64), BitwiseOperation::RightShift).unwrap(),
            Value::from(10)
        );

        assert_eq!(Value::bitwise_not(&l).unwrap(), Value::from(-11));
        assert_eq!(
            Value::bitwise_not(&Value::from(0u8)).unwrap(),
            Value::u8(255)
        );
        assert_eq!(
            Value::bitwise_not(&Value::from(1)).unwrap(),
            Value::from(-2)
        );

        assert_eq!(
            Value::bitwise_not(&Value::from(0u8)).unwrap(),
            Value::from(u8::MAX)
        );
        assert_eq!(
            Value::bitwise_not(&Value::from(0u16)).unwrap(),
            Value::from(u16::MAX)
        );
        assert_eq!(
            Value::bitwise_not(&Value::from(0u32)).unwrap(),
            Value::from(u32::MAX)
        );
        assert_eq!(
            Value::bitwise_not(&Value::from(0u64)).unwrap(),
            Value::from(u64::MAX)
        );
        assert_eq!(
            Value::bitwise_not(&Value::from(0i8)).unwrap(),
            Value::from((-1) as i8)
        );
        assert_eq!(
            Value::bitwise_not(&Value::from(0i16)).unwrap(),
            Value::from((-1) as i16)
        );
        assert_eq!(
            Value::bitwise_not(&Value::from(I32::new(0))).unwrap(),
            Value::from(I32::new(-1))
        );
        assert_eq!(
            Value::bitwise_not(&Value::from(I64::new(0))).unwrap(),
            Value::from(I64::new(-1))
        );
    }

    #[test]
    fn test_serialize() {
        let value = serde_json::to_value(Value::from(1.0)).unwrap();
        assert_eq!(value, serde_json::json!(1.0));

        let value = serde_json::to_value(Value::from(1)).unwrap();
        assert_eq!(value, serde_json::json!(1));

        let value = serde_json::to_value(Value::from("abc")).unwrap();
        assert_eq!(value, serde_json::json!("abc"));

        let value = serde_json::to_value(Value::from(vec![Value::from(1)])).unwrap();
        assert_eq!(value, serde_json::json!([1]));

        let value = serde_json::to_value(
            Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap(),
        )
        .unwrap();
        assert_eq!(value, serde_json::json!([["a", 1]]));
    }
}
