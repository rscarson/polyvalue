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

    /// Consumes the value and returns the inner value
    fn into_inner(self) -> Self::Inner;
}

/// Main value type
/// This is an enum that can hold any of the supported value types
#[derive(Clone, Serialize, Deserialize, Eq, Hash, PartialEq)]
#[serde(untagged)]
pub enum InnerValue {
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

/// Main value type
/// This is an enum that can hold any of the supported value types
#[derive(Clone, Eq, Hash, PartialEq)]
pub struct Value {
    inner: InnerValue,
    flags: u8,
}

impl Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.inner.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Value {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        InnerValue::deserialize(deserializer).map(|inner| Value { inner, flags: 0 })
    }
}

impl TryFrom<serde_json::Value> for Value {
    type Error = Error;
    fn try_from(value: serde_json::Value) -> Result<Self, Self::Error> {
        match value {
            serde_json::Value::Null => Ok(Value::string("")),
            serde_json::Value::Bool(v) => Ok(Value::bool(v)),
            serde_json::Value::String(v) => Ok(Value::string(v)),
            serde_json::Value::Array(v) => Ok(v
                .into_iter()
                .map(|v| Value::try_from(v))
                .collect::<Result<Vec<_>, _>>()?
                .into()),
            serde_json::Value::Object(v) => {
                let mut object = ObjectInner::new();
                for (key, value) in v {
                    object.insert(Value::from(key), Value::try_from(value)?)?;
                }
                Ok(Value::object(object))
            }
            serde_json::Value::Number(v) => {
                if v.is_f64() {
                    Ok(Value::from(v.as_f64().unwrap()))
                } else if v.is_i64() {
                    Ok(Value::from(v.as_i64().unwrap()))
                } else if v.is_u64() {
                    Ok(Value::from(v.as_u64().unwrap()))
                } else {
                    Err(Error::ValueConversion {
                        src_type: ValueType::Numeric,
                        dst_type: ValueType::Int,
                    })
                }
            }
        }
    }
}

impl From<Value> for InnerValue {
    fn from(value: Value) -> InnerValue {
        value.inner
    }
}

impl From<InnerValue> for Value {
    fn from(inner: InnerValue) -> Value {
        Value { inner, flags: 0 }
    }
}

impl Value {
    /// Creates a new value from the given inner value
    pub fn new(inner: InnerValue) -> Self {
        Self { inner, flags: 0 }
    }

    /// Consumes the value and returns the inner value
    pub fn into_inner(self) -> InnerValue {
        self.inner
    }

    /// Returns a reference to the inner value
    pub fn inner(&self) -> &InnerValue {
        &self.inner
    }

    /// Returns a mutable reference to the inner value
    pub fn inner_mut(&mut self) -> &mut InnerValue {
        &mut self.inner
    }

    /// Set a flag on the value
    pub fn set_flag(&mut self, flag: u8) {
        self.flags |= flag;
    }

    /// Clears the given flag
    pub fn clear_flag(&mut self, flag: u8) {
        self.flags &= !flag;
    }

    /// Returns true if the value has the given flag
    pub fn has_flag(&self, flag: u8) -> bool {
        self.flags & flag != 0
    }

    /// Serializes the value to a tagged value
    /// This is useful for serialization, as it will preserve the type of integers
    pub fn serialize_tagged(self) -> Result<String, serde_json::Error> {
        Ok(TaggedValue::from(self).serialize()?.to_string())
    }

    /// Deserializes a tagged value
    pub fn deserialize_tagged(value: &str) -> Result<Self, serde_json::Error> {
        TaggedValue::deserialize(&serde_json::Value::from_str(value)?).map(|x| x.into())
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn bool(inner: impl Into<Bool>) -> Self {
        InnerValue::Bool(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn u8(inner: impl Into<U8>) -> Self {
        InnerValue::U8(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn i8(inner: impl Into<I8>) -> Self {
        InnerValue::I8(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn u16(inner: impl Into<U16>) -> Self {
        InnerValue::U16(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn i16(inner: impl Into<I16>) -> Self {
        InnerValue::I16(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn u32(inner: impl Into<U32>) -> Self {
        InnerValue::U32(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn i32(inner: impl Into<I32>) -> Self {
        InnerValue::I32(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn u64(inner: impl Into<U64>) -> Self {
        InnerValue::U64(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn i64(inner: impl Into<I64>) -> Self {
        InnerValue::I64(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn float(inner: impl Into<Float>) -> Self {
        InnerValue::Float(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn fixed(inner: impl Into<Fixed>) -> Self {
        InnerValue::Fixed(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn currency(inner: impl Into<Currency>) -> Self {
        InnerValue::Currency(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn string(inner: impl Into<Str>) -> Self {
        InnerValue::String(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn range(inner: impl Into<Range>) -> Self {
        InnerValue::Range(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn array(inner: impl Into<Array>) -> Self {
        InnerValue::Array(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn object(inner: impl Into<Object>) -> Self {
        InnerValue::Object(inner.into()).into()
    }

    /// Creates a new value from the given inner value
    /// Use with the types defined in [`crate::types`]
    pub fn int(inner: impl Into<I64>) -> Self {
        InnerValue::I64(inner.into()).into()
    }

    /// Resolves the type of two values based on a priority system.
    /// If successful, both returned values are guaranteed to be of
    /// the same type
    ///
    /// Consumes both values
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
    /// let (a, b) = a.resolve(b).expect("Could not resolve types");
    /// assert!(a.own_type() == ValueType::Float);
    /// assert!(b.own_type() == ValueType::Float);
    /// ```
    pub fn resolve(self, other: Self) -> Result<(Value, Value), Error> {
        let values = match self.type_for_comparison(&other) {
            ValueType::Bool => (Bool::try_from(self)?.into(), Bool::try_from(other)?.into()),

            ValueType::Fixed => (
                Fixed::try_from(self)?.into(),
                Fixed::try_from(other)?.into(),
            ),

            ValueType::Float => (
                Float::try_from(self)?.into(),
                Float::try_from(other)?.into(),
            ),

            ValueType::Currency => {
                let values: (Currency, Currency) =
                    (Currency::try_from(self)?, Currency::try_from(other)?);

                // Resolve symbols and precisions too
                let values = values.0.resolve(values.1);

                (values.0.into(), values.1.into())
            }

            ValueType::U8 => (U8::try_from(self)?.into(), U8::try_from(other)?.into()),
            ValueType::U16 => (U16::try_from(self)?.into(), U16::try_from(other)?.into()),
            ValueType::U32 => (U32::try_from(self)?.into(), U32::try_from(other)?.into()),
            ValueType::U64 => (U64::try_from(self)?.into(), U64::try_from(other)?.into()),
            ValueType::I8 => (I8::try_from(self)?.into(), I8::try_from(other)?.into()),
            ValueType::I16 => (I16::try_from(self)?.into(), I16::try_from(other)?.into()),
            ValueType::I32 => (I32::try_from(self)?.into(), I32::try_from(other)?.into()),
            ValueType::I64 => (I64::try_from(self)?.into(), I64::try_from(other)?.into()),

            ValueType::Array => (
                Array::try_from(self)?.into(),
                Array::try_from(other)?.into(),
            ),

            ValueType::Object => (
                Object::try_from(self)?.into(),
                Object::try_from(other)?.into(),
            ),

            ValueType::String => (Str::try_from(self)?.into(), Str::try_from(other)?.into()),

            ValueType::Range => (
                Range::try_from(self)?.into(),
                Range::try_from(other)?.into(),
            ),

            ValueType::Int | ValueType::Numeric | ValueType::Collection | ValueType::Any => {
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
        match self.inner() {
            InnerValue::Bool(_) => ValueType::Bool,
            InnerValue::Fixed(_) => ValueType::Fixed,
            InnerValue::Float(_) => ValueType::Float,
            InnerValue::Currency(_) => ValueType::Currency,
            InnerValue::U8(_) => ValueType::U8,
            InnerValue::U16(_) => ValueType::U16,
            InnerValue::U32(_) => ValueType::U32,
            InnerValue::U64(_) => ValueType::U64,
            InnerValue::I8(_) => ValueType::I8,
            InnerValue::I16(_) => ValueType::I16,
            InnerValue::I32(_) => ValueType::I32,
            InnerValue::I64(_) => ValueType::I64,
            InnerValue::String(_) => ValueType::String,
            InnerValue::Range(_) => ValueType::Range,
            InnerValue::Array(_) => ValueType::Array,
            InnerValue::Object(_) => ValueType::Object,
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
    pub fn as_a<T>(self) -> Result<T, Error>
    where
        Self: TryInto<T, Error = Error>,
    {
        self.try_into()
    }

    /// Resolves a value to the given type, if the type matches a condition
    /// Use with the types defined in [`crate::types`]
    /// Returns None if the type does not match
    ///
    /// # Example
    /// ```rust
    /// use polyvalue::{ValueType, Value};
    ///
    /// let value = Value::from(1.0);
    /// if let Some(value) = value.if_is_a::<i64>(ValueType::Numeric) {
    ///    println!("Value is a number: {}", value);
    /// }
    pub fn if_is_a<T>(&self, type_name: ValueType) -> Option<T>
    where
        Self: TryInto<T, Error = Error>,
    {
        if self.is_a(type_name) {
            self.clone().try_into().ok()
        } else {
            None
        }
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
                ValueType::Collection,
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
    /// For collection, the value will be converted to object
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
    pub fn as_type(self, type_name: ValueType) -> Result<Value, Error> {
        let value = match type_name {
            ValueType::Bool => Bool::try_from(self)?.into(),
            ValueType::Fixed => Fixed::try_from(self)?.into(),
            ValueType::Float => Float::try_from(self)?.into(),
            ValueType::Currency => Currency::try_from(self)?.into(),

            ValueType::U8 => U8::try_from(self)?.into(),
            ValueType::U16 => U16::try_from(self)?.into(),
            ValueType::U32 => U32::try_from(self)?.into(),
            ValueType::U64 => U64::try_from(self)?.into(),
            ValueType::I8 => I8::try_from(self)?.into(),
            ValueType::I16 => I16::try_from(self)?.into(),
            ValueType::I32 => I32::try_from(self)?.into(),
            ValueType::I64 => I64::try_from(self)?.into(),

            ValueType::String => Str::try_from(self)?.into(),
            ValueType::Array => Array::try_from(self)?.into(),
            ValueType::Object => Object::try_from(self)?.into(),

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

            ValueType::Collection => {
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
                (ValueType::Object, _) | (_, ValueType::Object) => ValueType::Object,
                (ValueType::Array, _) | (_, ValueType::Array) => ValueType::Array,
                (ValueType::String, _) | (_, ValueType::String) => ValueType::String,
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
                | (ValueType::Collection, _)
                | (ValueType::Any, _) => {
                    unreachable!(
                        "Non-concrete type encountered in resolve: {:?}",
                        self.own_type()
                    )
                }
            }
        }
    }

    /// Returns true if the value is truthy
    /// This is a convenience method for boolean values
    pub fn is_truthy(&self) -> bool {
        Bool::is_truthy(self)
    }

    /// Returns the length of the value
    /// For strings, this is the length of the string in characters
    /// For collection types, this is the number of elements
    /// For everything else, this is 1 (the length of the array it would resolve to)
    pub fn len(&self) -> usize {
        match self.inner() {
            InnerValue::String(v) => v.len(),
            InnerValue::Range(v) => v.len() as usize,
            InnerValue::Array(v) => v.len(),
            InnerValue::Object(v) => v.len(),

            _ => 1,
        }
    }

    /// Returns the value as a JSON string
    /// Returned value should be valid JSON
    pub fn to_json_string(&self) -> String {
        match self.inner() {
            InnerValue::Currency(v) => format!("\"{}\"", v.to_string()),
            InnerValue::String(v) => v.to_escaped_string(),
            InnerValue::Array(v) => {
                format!(
                    "[{}]",
                    v.iter()
                        .map(|x| x.to_json_string())
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
            InnerValue::Object(v) => {
                format!(
                    "{{{}}}",
                    v.iter()
                        .map(|(k, v)| format!("{}:{}", k.to_json_string(), v.to_json_string()))
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }

            _ => self.to_string(),
        }
    }

    /// Compares two values, ignoring type
    /// Consumes both values
    pub fn weak_equality(self, other: Self) -> Result<bool, Error> {
        let (l, r) = self.resolve(other)?;
        Ok(l == r)
    }

    /// Compares two values, ignoring type
    /// Consumes both values
    pub fn weak_ord(self, other: Self) -> Result<std::cmp::Ordering, Error> {
        let (l, r) = self.resolve(other)?;

        Ok(match (l.into_inner(), r.into_inner()) {
            (InnerValue::Bool(l), InnerValue::Bool(r)) => l.cmp(&r),
            (InnerValue::Fixed(l), InnerValue::Fixed(r)) => l.cmp(&r),
            (InnerValue::Float(l), InnerValue::Float(r)) => l.cmp(&r),
            (InnerValue::Currency(l), InnerValue::Currency(r)) => l.cmp(&r),

            (InnerValue::U8(l), InnerValue::U8(r)) => l.cmp(&r),
            (InnerValue::U16(l), InnerValue::U16(r)) => l.cmp(&r),
            (InnerValue::U32(l), InnerValue::U32(r)) => l.cmp(&r),
            (InnerValue::U64(l), InnerValue::U64(r)) => l.cmp(&r),

            (InnerValue::I8(l), InnerValue::I8(r)) => l.cmp(&r),
            (InnerValue::I16(l), InnerValue::I16(r)) => l.cmp(&r),
            (InnerValue::I32(l), InnerValue::I32(r)) => l.cmp(&r),
            (InnerValue::I64(l), InnerValue::I64(r)) => l.cmp(&r),

            (InnerValue::String(l), InnerValue::String(r)) => l.cmp(&r),
            (InnerValue::Range(l), InnerValue::Range(r)) => l.cmp(&r),
            (InnerValue::Array(l), InnerValue::Array(r)) => l.cmp(&r),
            (InnerValue::Object(l), InnerValue::Object(r)) => l.cmp(&r),

            _ => unreachable!("`resolve()` should have resolved both values to the same type"),
        })
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner() {
            InnerValue::Bool(v) => write!(f, "{}", v),
            InnerValue::Fixed(v) => write!(f, "{}", v),
            InnerValue::Float(v) => write!(f, "{}", v),
            InnerValue::Currency(v) => write!(f, "{}", v),

            InnerValue::U8(v) => write!(f, "{}", v),
            InnerValue::U16(v) => write!(f, "{}", v),
            InnerValue::U32(v) => write!(f, "{}", v),
            InnerValue::U64(v) => write!(f, "{}", v),

            InnerValue::I8(v) => write!(f, "{}", v),
            InnerValue::I16(v) => write!(f, "{}", v),
            InnerValue::I32(v) => write!(f, "{}", v),
            InnerValue::I64(v) => write!(f, "{}", v),

            InnerValue::String(v) => write!(f, "{}", v),
            InnerValue::Range(v) => write!(f, "{}", v),
            InnerValue::Array(v) => write!(f, "{}", v),
            InnerValue::Object(v) => write!(f, "{}", v),
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner() {
            InnerValue::Bool(v) => write!(f, "{:?}", v),
            InnerValue::Fixed(v) => write!(f, "{:?}", v),
            InnerValue::Float(v) => write!(f, "{:?}", v),
            InnerValue::Currency(v) => write!(f, "{:?}", v),

            InnerValue::U8(v) => write!(f, "{:?}", v),
            InnerValue::U16(v) => write!(f, "{:?}", v),
            InnerValue::U32(v) => write!(f, "{:?}", v),
            InnerValue::U64(v) => write!(f, "{:?}", v),

            InnerValue::I8(v) => write!(f, "{:?}", v),
            InnerValue::I16(v) => write!(f, "{:?}", v),
            InnerValue::I32(v) => write!(f, "{:?}", v),
            InnerValue::I64(v) => write!(f, "{:?}", v),

            InnerValue::String(v) => write!(f, "{:?}", v),
            InnerValue::Range(v) => write!(f, "{:?}", v),
            InnerValue::Array(v) => write!(f, "{:?}", v),
            InnerValue::Object(v) => write!(f, "{:?}", v),
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self.inner(), other.inner()) {
            (InnerValue::Bool(v), InnerValue::Bool(v2)) => Some(v.cmp(v2)),
            (InnerValue::U8(v), InnerValue::U8(v2)) => Some(v.cmp(v2)),
            (InnerValue::I8(v), InnerValue::I8(v2)) => Some(v.cmp(v2)),
            (InnerValue::U16(v), InnerValue::U16(v2)) => Some(v.cmp(v2)),
            (InnerValue::I16(v), InnerValue::I16(v2)) => Some(v.cmp(v2)),
            (InnerValue::U32(v), InnerValue::U32(v2)) => Some(v.cmp(v2)),
            (InnerValue::I32(v), InnerValue::I32(v2)) => Some(v.cmp(v2)),
            (InnerValue::U64(v), InnerValue::U64(v2)) => Some(v.cmp(v2)),
            (InnerValue::I64(v), InnerValue::I64(v2)) => Some(v.cmp(v2)),
            (InnerValue::Fixed(v), InnerValue::Fixed(v2)) => v.partial_cmp(v2),
            (InnerValue::Float(v), InnerValue::Float(v2)) => v.partial_cmp(v2),
            (InnerValue::Currency(v), InnerValue::Currency(v2)) => v.partial_cmp(v2),
            (InnerValue::String(v), InnerValue::String(v2)) => v.partial_cmp(v2),
            (InnerValue::Range(v), InnerValue::Range(v2)) => v.partial_cmp(v2),
            (InnerValue::Array(v), InnerValue::Array(v2)) => v.partial_cmp(v2),
            (InnerValue::Object(v), InnerValue::Object(v2)) => v.partial_cmp(v2),

            (InnerValue::Bool(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::Bool(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::U8(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::U8(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::I8(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::I8(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::U16(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::U16(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::I16(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::I16(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::U32(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::U32(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::I32(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::I32(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::U64(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::U64(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::I64(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::I64(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::Float(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::Float(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::Fixed(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::Fixed(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::Currency(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::Currency(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::String(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::String(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::Range(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::Range(_)) => Some(std::cmp::Ordering::Greater),

            (InnerValue::Array(_), _) => Some(std::cmp::Ordering::Less),
            (_, InnerValue::Array(_)) => Some(std::cmp::Ordering::Greater),
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
    fn boolean_op(self, right: Self, operation: BooleanOperation) -> Result<Self, Error> {
        if operation == BooleanOperation::StrictEQ && self.own_type() != right.own_type() {
            return Ok(Bool::from(false).into());
        } else if operation == BooleanOperation::StrictNEQ && self.own_type() != right.own_type() {
            return Ok(Bool::from(true).into());
        }

        let (left, right) = self.resolve(right)?;
        match (left.inner, right.inner) {
            (InnerValue::Bool(l), InnerValue::Bool(r)) => {
                Bool::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Fixed(l), InnerValue::Fixed(r)) => {
                Fixed::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Float(l), InnerValue::Float(r)) => {
                Float::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Currency(l), InnerValue::Currency(r)) => {
                Currency::boolean_op(l, r, operation).map(Into::into)
            }

            (InnerValue::U8(l), InnerValue::U8(r)) => {
                U8::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::U16(l), InnerValue::U16(r)) => {
                U16::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::U32(l), InnerValue::U32(r)) => {
                U32::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::U64(l), InnerValue::U64(r)) => {
                U64::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::I8(l), InnerValue::I8(r)) => {
                I8::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::I16(l), InnerValue::I16(r)) => {
                I16::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::I32(l), InnerValue::I32(r)) => {
                I32::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::I64(l), InnerValue::I64(r)) => {
                I64::boolean_op(l, r, operation).map(Into::into)
            }

            (InnerValue::String(l), InnerValue::String(r)) => {
                Str::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Array(l), InnerValue::Array(r)) => {
                Array::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Object(l), InnerValue::Object(r)) => {
                Object::boolean_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Range(l), InnerValue::Range(r)) => {
                Range::boolean_op(l, r, operation).map(Into::into)
            }

            _ => unreachable!("Invalid type combination for boolean operation"),
        }
    }

    fn boolean_not(self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        match self.inner {
            InnerValue::Bool(l) => Bool::boolean_not(l).map(Into::into),
            InnerValue::Fixed(l) => Fixed::boolean_not(l).map(Into::into),
            InnerValue::Float(l) => Float::boolean_not(l).map(Into::into),
            InnerValue::Currency(l) => Currency::boolean_not(l).map(Into::into),

            InnerValue::U8(l) => U8::boolean_not(l).map(Into::into),
            InnerValue::U16(l) => U16::boolean_not(l).map(Into::into),
            InnerValue::U32(l) => U32::boolean_not(l).map(Into::into),
            InnerValue::U64(l) => U64::boolean_not(l).map(Into::into),
            InnerValue::I8(l) => I8::boolean_not(l).map(Into::into),
            InnerValue::I16(l) => I16::boolean_not(l).map(Into::into),
            InnerValue::I32(l) => I32::boolean_not(l).map(Into::into),
            InnerValue::I64(l) => I64::boolean_not(l).map(Into::into),

            InnerValue::String(l) => Str::boolean_not(l).map(Into::into),
            InnerValue::Array(l) => Array::boolean_not(l).map(Into::into),
            InnerValue::Object(l) => Object::boolean_not(l).map(Into::into),
            InnerValue::Range(l) => Range::boolean_not(l).map(Into::into),
        }
    }
}

impl BitwiseOperationExt for Value {
    fn bitwise_op(self, right: Self, operation: BitwiseOperation) -> Result<Self, Error> {
        let (left, right) = self.resolve(right)?;

        if !left.is_a(ValueType::Int) {
            let left = left.as_a::<I64>()?;
            let right = right.as_a::<I64>()?;
            left.bitwise_op(right, operation).map(Into::into)
        } else {
            match (left.into_inner(), right.into_inner()) {
                (InnerValue::U8(l), InnerValue::U8(r)) => {
                    l.bitwise_op(r, operation).map(Into::into)
                }
                (InnerValue::U16(l), InnerValue::U16(r)) => {
                    l.bitwise_op(r, operation).map(Into::into)
                }
                (InnerValue::U32(l), InnerValue::U32(r)) => {
                    l.bitwise_op(r, operation).map(Into::into)
                }
                (InnerValue::U64(l), InnerValue::U64(r)) => {
                    l.bitwise_op(r, operation).map(Into::into)
                }
                (InnerValue::I8(l), InnerValue::I8(r)) => {
                    l.bitwise_op(r, operation).map(Into::into)
                }
                (InnerValue::I16(l), InnerValue::I16(r)) => {
                    l.bitwise_op(r, operation).map(Into::into)
                }
                (InnerValue::I32(l), InnerValue::I32(r)) => {
                    l.bitwise_op(r, operation).map(Into::into)
                }
                (InnerValue::I64(l), InnerValue::I64(r)) => {
                    l.bitwise_op(r, operation).map(Into::into)
                }

                _ => unreachable!("Invalid type combination for bitwise operation"),
            }
        }
    }

    fn bitwise_not(self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        match self.inner {
            InnerValue::U8(l) => U8::bitwise_not(l).map(Into::into),
            InnerValue::U16(l) => U16::bitwise_not(l).map(Into::into),
            InnerValue::U32(l) => U32::bitwise_not(l).map(Into::into),
            InnerValue::U64(l) => U64::bitwise_not(l).map(Into::into),
            InnerValue::I8(l) => I8::bitwise_not(l).map(Into::into),
            InnerValue::I16(l) => I16::bitwise_not(l).map(Into::into),
            InnerValue::I32(l) => I32::bitwise_not(l).map(Into::into),
            _ => self.as_a::<I64>()?.bitwise_not().map(Into::into),
        }
    }
}

impl ArithmeticOperationExt for Value {
    fn arithmetic_op(self, right: Self, operation: ArithmeticOperation) -> Result<Self, Error> {
        let (left, right) = self.resolve(right)?;
        match (left.inner, right.inner) {
            (InnerValue::Bool(l), InnerValue::Bool(r)) => {
                Bool::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Fixed(l), InnerValue::Fixed(r)) => {
                Fixed::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Float(l), InnerValue::Float(r)) => {
                Float::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Currency(l), InnerValue::Currency(r)) => {
                Currency::arithmetic_op(l, r, operation).map(Into::into)
            }

            (InnerValue::U8(l), InnerValue::U8(r)) => {
                U8::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::U16(l), InnerValue::U16(r)) => {
                U16::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::U32(l), InnerValue::U32(r)) => {
                U32::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::U64(l), InnerValue::U64(r)) => {
                U64::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::I8(l), InnerValue::I8(r)) => {
                I8::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::I16(l), InnerValue::I16(r)) => {
                I16::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::I32(l), InnerValue::I32(r)) => {
                I32::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::I64(l), InnerValue::I64(r)) => {
                I64::arithmetic_op(l, r, operation).map(Into::into)
            }

            (InnerValue::String(l), InnerValue::String(r)) => {
                Str::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Array(l), InnerValue::Array(r)) => {
                Array::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Object(l), InnerValue::Object(r)) => {
                Object::arithmetic_op(l, r, operation).map(Into::into)
            }
            (InnerValue::Range(l), InnerValue::Range(r)) => {
                Range::arithmetic_op(l, r, operation).map(Into::into)
            }
            _ => unreachable!("Invalid type combination during boolean operation"),
        }
    }

    fn arithmetic_neg(self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        match self.inner {
            InnerValue::Bool(l) => Bool::arithmetic_neg(l).map(Into::into),
            InnerValue::Fixed(l) => Fixed::arithmetic_neg(l).map(Into::into),
            InnerValue::Float(l) => Float::arithmetic_neg(l).map(Into::into),
            InnerValue::Currency(l) => Currency::arithmetic_neg(l).map(Into::into),

            InnerValue::U8(l) => U8::arithmetic_neg(l).map(Into::into),
            InnerValue::U16(l) => U16::arithmetic_neg(l).map(Into::into),
            InnerValue::U32(l) => U32::arithmetic_neg(l).map(Into::into),
            InnerValue::U64(l) => U64::arithmetic_neg(l).map(Into::into),
            InnerValue::I8(l) => I8::arithmetic_neg(l).map(Into::into),
            InnerValue::I16(l) => I16::arithmetic_neg(l).map(Into::into),
            InnerValue::I32(l) => I32::arithmetic_neg(l).map(Into::into),
            InnerValue::I64(l) => I64::arithmetic_neg(l).map(Into::into),

            InnerValue::String(l) => Str::arithmetic_neg(l).map(Into::into),
            InnerValue::Array(l) => Array::arithmetic_neg(l).map(Into::into),
            InnerValue::Object(l) => Object::arithmetic_neg(l).map(Into::into),
            InnerValue::Range(l) => Range::arithmetic_neg(l).map(Into::into),
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
            let type_name = pattern.clone().as_a::<String>()?;
            let value_type = ValueType::try_from(type_name.as_str())?;
            Ok(container.is_a(value_type).into())
        } else {
            match container.own_type() {
                ValueType::Array => {
                    Array::matching_op(&container.clone().as_a::<Array>()?, pattern, operation)
                }

                ValueType::Object => {
                    Object::matching_op(&container.clone().as_a::<Object>()?, pattern, operation)
                }

                ValueType::Range => {
                    Range::matching_op(&container.clone().as_a::<Range>()?, pattern, operation)
                }

                _ => Str::matching_op(&container.clone().as_a::<Str>()?, pattern, operation),
            }
        }
    }
}

impl IndexingOperationExt for Value {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        match self.inner() {
            InnerValue::Array(v) => v.get_index(index),
            InnerValue::Object(v) => v.get_index(index),
            InnerValue::Range(v) => v.get_index(index),
            InnerValue::String(v) => v.get_index(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Collection,
            })?,
        }
    }

    fn get_indices(&self, index: &Value) -> Result<Value, crate::Error> {
        match self.inner() {
            InnerValue::Array(v) => v.get_indices(index),
            InnerValue::Object(v) => v.get_indices(index),
            InnerValue::Range(v) => v.get_indices(index),
            InnerValue::String(v) => v.get_indices(index),

            _ => Err(Error::ValueType {
                actual_type: self.own_type(),
                expected_type: ValueType::Collection,
            })?,
        }
    }
}

impl IndexingMutationExt for Value {
    fn get_index_mut(&mut self, index: &Value) -> Result<&mut Value, crate::Error> {
        let _type = self.own_type();
        match self.inner_mut() {
            InnerValue::Array(v) => v.get_index_mut(index),
            InnerValue::Object(v) => v.get_index_mut(index),

            _ => Err(Error::ValueType {
                actual_type: _type,
                expected_type: ValueType::Collection,
            })?,
        }
    }

    fn get_indices_mut(&mut self, index: &Value) -> Result<Vec<&mut Value>, crate::Error> {
        let _type = self.own_type();
        match self.inner_mut() {
            InnerValue::Array(v) => v.get_indices_mut(index),
            InnerValue::Object(v) => v.get_indices_mut(index),

            _ => Err(Error::ValueType {
                actual_type: _type,
                expected_type: ValueType::Collection,
            })?,
        }
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        let _type = self.own_type();
        match self.inner_mut() {
            InnerValue::Array(v) => v.set_index(index, value),
            InnerValue::Object(v) => v.set_index(index, value),

            _ => Err(Error::ValueType {
                actual_type: _type,
                expected_type: ValueType::Collection,
            })?,
        }
    }

    fn insert_at(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        let _type = self.own_type();
        match self.inner_mut() {
            InnerValue::Array(v) => v.insert_at(index, value),
            InnerValue::Object(v) => v.insert_at(index, value),

            _ => Err(Error::ValueType {
                actual_type: _type,
                expected_type: ValueType::Collection,
            })?,
        }
    }

    fn delete_index(&mut self, index: &Value) -> Result<Value, crate::Error> {
        let _type = self.own_type();
        match self.inner_mut() {
            InnerValue::Array(v) => v.delete_index(index),
            InnerValue::Object(v) => v.delete_index(index),

            _ => Err(Error::ValueType {
                actual_type: _type,
                expected_type: ValueType::Collection,
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
    fn test_to_json_string() {
        let value = Value::from(1.0);
        assert_eq!(value.to_json_string(), "1.0");

        let value = Value::from("abc");
        assert_eq!(value.to_json_string(), r#""abc""#);

        let value = Value::from(vec![Value::from(1.0), Value::from(2.0)]);
        assert_eq!(value.to_json_string(), r#"[1.0,2.0]"#);

        let value = Value::try_from(vec![(Value::from("a"), Value::from(1.0))]).unwrap();
        assert_eq!(value.to_json_string(), r#"{"a":1.0}"#);

        let value = Value::from(1..=2);
        assert_eq!(value.to_json_string(), r#"1..2"#);
    }

    #[test]
    fn test_tagged_serialization() {
        let value = Value::from(1.0);
        let serialized = serde_json::to_string(&value).unwrap();
        assert_eq!(serialized, "1.0");
        let deserialized: Value = serde_json::from_str(&serialized).unwrap();
        assert_eq!(value, deserialized);

        let serialized = value.clone().serialize_tagged().unwrap();
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
            value
                .clone()
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("bool")),
            Some(&Value::from(true))
        );
        assert_eq!(
            value
                .clone()
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("fixed")),
            Some(&Value::from(1.0))
        );
        assert_eq!(
            value
                .clone()
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("float")),
            Some(&Value::from(1.0))
        );
        assert_eq!(
            value
                .clone()
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("currency")),
            Some(&Value::from(1.0))
        );
        assert_eq!(
            value
                .clone()
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("int")),
            Some(&Value::from(1i64))
        );
        assert_eq!(
            value
                .clone()
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("string")),
            Some(&Value::from("abc"))
        );
        assert_eq!(
            value
                .clone()
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("array")),
            Some(&Value::from(vec![
                Value::i64(1),
                Value::i64(2),
                Value::i64(3)
            ]))
        );
        assert_eq!(
            value
                .clone()
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("range")),
            Some(&Value::from(vec![
                Value::i64(1),
                Value::i64(2),
                Value::i64(3)
            ]))
        );
        assert_eq!(
            value
                .clone()
                .as_a::<Object>()
                .unwrap()
                .get(&Value::from("null")),
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
        let pattern = Value::from(1.0);
        let result = Value::matching_op(&value, &pattern, MatchingOperation::Contains).unwrap();
        assert_eq!(result, Value::from(true));

        let value = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        let pattern = Value::from("a");
        let result = Value::matching_op(&value, &pattern, MatchingOperation::Contains).unwrap();
        assert_eq!(result, Value::from(true));

        let value = Value::from(Range::from(1..=2));
        let pattern = Value::from(1);
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
        let (a, b) = a.resolve(b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Float);
        assert!(b.own_type() == ValueType::Float);

        let a = Value::from(Fixed::zero());
        let b = Value::from(2);
        let (a, b) = a.resolve(b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Fixed);
        assert!(b.own_type() == ValueType::Fixed);

        let a = Value::from(false);
        let b = Value::from(true);
        let (a, b) = a.resolve(b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Bool);
        assert!(b.own_type() == ValueType::Bool);

        let a = Value::from(1);
        let b = Value::from(2);
        let (a, b) = a.resolve(b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::I32);
        assert!(b.own_type() == ValueType::I32);

        let a = Value::from("abc");
        let b = Value::from(2);
        let (a, b) = a.resolve(b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::String);
        assert!(b.own_type() == ValueType::String);

        let a = Value::from(1);
        let b = Value::from(vec![Value::from(1)]);
        let (a, b) = a.resolve(b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Array);
        assert!(b.own_type() == ValueType::Array);

        let a = Value::from(vec![Value::from(1)]);
        let b = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        let (a, b) = a.resolve(b).expect("Could not resolve types");
        assert!(a.own_type() == ValueType::Object);
        assert!(b.own_type() == ValueType::Object);

        let a = Value::from(CurrencyInner::as_dollars(Fixed::zero()));
        let b = Value::from(Fixed::zero());
        let (a, b) = a.resolve(b).expect("Could not resolve types");
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
            Value::from(CurrencyInner::as_dollars(Fixed::zero())).own_type(),
            ValueType::Currency
        );

        assert_eq!(Value::from(Fixed::zero()).own_type(), ValueType::Fixed);

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
        assert!(a.either_type(&b, ValueType::Collection));
    }

    #[test]
    fn test_as_a() {
        let value = Value::from(1.0);
        assert_eq!(value.clone().as_a::<String>().unwrap(), "1.0".to_string());
        assert_eq!(value.as_a::<bool>().unwrap(), true);

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
        assert!(value.is_a(ValueType::Collection));
        assert!(!value.is_a(ValueType::Object));

        assert!(Value::from(1).is_a(ValueType::Numeric));
        assert!(Value::from(1).is_a(ValueType::Any));

        assert!(Value::from(1.0).is_a(ValueType::Numeric));
        assert!(Value::from(Fixed::zero()).is_a(ValueType::Numeric));
        assert!(Value::from(CurrencyInner::as_dollars(Fixed::zero())).is_a(ValueType::Numeric));
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
            .as_type(ValueType::Collection)
            .expect("Value could not be converted to collection!");
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

        let value = Value::from(CurrencyInner::as_dollars(Fixed::zero()));
        assert_eq!(
            value.as_type(ValueType::Numeric).unwrap(),
            Value::from(CurrencyInner::as_dollars(Fixed::zero()))
        );

        let value = Value::from(Fixed::zero());
        assert_eq!(
            value.as_type(ValueType::Numeric).unwrap(),
            Value::from(Fixed::zero())
        );

        assert_eq!(
            Value::from(1).as_type(ValueType::Bool).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Value::from(0).as_type(ValueType::Fixed).unwrap(),
            Value::from(Fixed::zero())
        );

        assert_eq!(
            Value::from(0).as_type(ValueType::Currency).unwrap(),
            Value::from(CurrencyInner::from_fixed(Fixed::zero()))
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
            .as_type(ValueType::Collection)
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
            CurrencyInner::as_dollars(Fixed::zero()),
            ValueType::Currency
        );

        assert_type_for_comparison!(
            CurrencyInner::as_dollars(Fixed::zero()),
            Fixed::zero(),
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
            "{\"a\": 1}"
        );

        assert_eq!(Value::from(true).to_string(), "true");
        assert_eq!(Value::from(false).to_string(), "false");

        assert_eq!(
            Value::from(CurrencyInner::as_dollars(Fixed::zero())).to_string(),
            "0.00$"
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
            ObjectInner::try_from(vec![(0i64, 1), (1i64, 2)]).unwrap()
        );

        assert_ord!(
            1..=2,
            ObjectInner::try_from(vec![(0i64, 1i64), (1i64, 2i64)]).unwrap()
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
        assert!(Value::from(1.0).weak_equality(Value::from(1)).unwrap());

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
            Value::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Add).unwrap(),
            Value::from(15.0)
        );

        assert_eq!(
            Value::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Subtract).unwrap(),
            Value::from(5.0)
        );

        assert_eq!(
            Value::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Multiply).unwrap(),
            Value::from(50.0)
        );

        assert_eq!(
            Value::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Divide).unwrap(),
            Value::from(2.0)
        );

        assert_eq!(
            Value::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Modulo).unwrap(),
            Value::from(0.0)
        );

        assert_eq!(
            Value::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Exponentiate).unwrap(),
            Value::from(100000.0)
        );

        assert_eq!(Value::arithmetic_neg(a).unwrap(), Value::from(-10));

        Value::arithmetic_neg(Value::from("test")).unwrap();
        Value::arithmetic_neg(Value::from(false)).unwrap();
        Value::arithmetic_neg(Value::from(1)).unwrap();
        Value::arithmetic_neg(Value::from(1.0)).unwrap();
        Value::arithmetic_neg(Value::from(Fixed::zero())).unwrap();
        Value::arithmetic_neg(Value::from(CurrencyInner::as_dollars(Fixed::zero()))).unwrap();
        Value::arithmetic_op(Value::from(1u8), Value::from(1u8), ArithmeticOperation::Add).unwrap();
        Value::arithmetic_op(
            Value::from(1u16),
            Value::from(1u8),
            ArithmeticOperation::Add,
        )
        .unwrap();
        Value::arithmetic_op(
            Value::from(1u32),
            Value::from(1u8),
            ArithmeticOperation::Add,
        )
        .unwrap();
        Value::arithmetic_op(
            Value::from(1u64),
            Value::from(1u8),
            ArithmeticOperation::Add,
        )
        .unwrap();

        Value::arithmetic_neg(Value::from(1i8)).unwrap();
        Value::arithmetic_neg(Value::from(1i16)).unwrap();
        Value::arithmetic_neg(Value::from(I32::new(1))).unwrap();
        Value::arithmetic_neg(Value::from(I64::new(1))).unwrap();

        let a = Value::from(vec![Value::from(1), Value::from(2)]);
        let b = Value::from(vec![Value::from(3), Value::from(4)]);
        Value::arithmetic_op(a, b, ArithmeticOperation::Add).unwrap();

        let a = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        let b = Value::try_from(vec![(Value::from("b"), Value::from(2))]).unwrap();
        Value::arithmetic_op(a, b, ArithmeticOperation::Add).unwrap();

        let a = Value::from(1..=2);
        let b = Value::from(3..=4);
        Value::arithmetic_op(a, b, ArithmeticOperation::Add).unwrap_err();
    }

    #[test]
    fn test_boolean_logic() {
        let a = Value::from(true);
        let b = Value::from(0);

        assert_eq!(
            Value::from(false)
                .boolean_op(Value::from(0), BooleanOperation::EQ)
                .unwrap()
                .is_truthy(),
            true
        );
        assert_eq!(
            Value::from(false)
                .boolean_op(Value::from(0), BooleanOperation::StrictEQ)
                .unwrap()
                .is_truthy(),
            false
        );
        assert_eq!(
            Value::from(false)
                .boolean_op(Value::from(0), BooleanOperation::NEQ)
                .unwrap()
                .is_truthy(),
            false
        );
        assert_eq!(
            Value::from(false)
                .boolean_op(Value::from(0), BooleanOperation::StrictNEQ)
                .unwrap()
                .is_truthy(),
            true
        );

        assert_eq!(
            Value::boolean_op(a.clone(), b.clone(), BooleanOperation::And).unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Value::boolean_op(a.clone(), b.clone(), BooleanOperation::Or).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Value::boolean_op(a.clone(), b.clone(), BooleanOperation::LT).unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Value::boolean_op(a.clone(), b.clone(), BooleanOperation::GT).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Value::boolean_op(a.clone(), b.clone(), BooleanOperation::LTE).unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Value::boolean_op(a.clone(), b.clone(), BooleanOperation::GTE).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Value::boolean_op(a.clone(), b.clone(), BooleanOperation::EQ).unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Value::boolean_op(a.clone(), b.clone(), BooleanOperation::NEQ).unwrap(),
            Value::from(true)
        );

        assert_eq!(Value::boolean_not(a).unwrap(), Value::from(false));

        // fixed, float, and currency - boolean_not
        let a = Value::from(1.0);
        assert_eq!(Value::boolean_not(a).unwrap(), Value::from(false));
        let a = Value::from(Fixed::zero());
        assert_eq!(Value::boolean_not(a).unwrap(), Value::from(true));
        let a = Value::from(CurrencyInner::as_dollars(Fixed::zero()));
        assert_eq!(Value::boolean_not(a).unwrap(), Value::from(true));

        // string, array, object, range - boolean_not
        let a = Value::from("abc");
        assert_eq!(Value::boolean_not(a).unwrap(), Value::from(false));
        let a = Value::from(vec![Value::from(1)]);
        assert_eq!(Value::boolean_not(a).unwrap(), Value::from(false));
        let a = Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap();
        assert_eq!(Value::boolean_not(a).unwrap(), Value::from(false));
        let a = Value::from(1..=2);
        assert_eq!(Value::boolean_not(a).unwrap(), Value::from(false));

        // u8, i8, u16, i16, u32, i32, u64, i64 - boolean_not
        assert_eq!(
            Value::boolean_not(Value::from(1u8)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(Value::from(1i8)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(Value::from(1u16)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(Value::from(1i16)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(Value::from(1u32)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(Value::from(I32::new(1))).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(Value::from(I64::new(1))).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(Value::from(1u64)).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Value::boolean_not(Value::from(1i64)).unwrap(),
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
            Value::bitwise_op(l.clone(), r.clone(), BitwiseOperation::And).unwrap(),
            Value::from(0b1000)
        );

        assert_eq!(
            Value::bitwise_op(l.clone(), r.clone(), BitwiseOperation::Or).unwrap(),
            Value::from(0b1110)
        );

        assert_eq!(
            Value::bitwise_op(l.clone(), r.clone(), BitwiseOperation::Xor).unwrap(),
            Value::from(0b0110)
        );

        assert_eq!(
            Value::bitwise_op(l.clone(), Value::from(2), BitwiseOperation::LeftShift).unwrap(),
            Value::from(0b101000)
        );

        assert_eq!(
            Value::bitwise_op(l.clone(), Value::from(-2), BitwiseOperation::LeftShift).unwrap(),
            Value::from(2)
        );

        assert_eq!(
            Value::bitwise_op(l.clone(), Value::from(2000), BitwiseOperation::LeftShift).unwrap(),
            Value::from(655360)
        );

        assert_eq!(
            Value::bitwise_op(l.clone(), Value::from(2), BitwiseOperation::RightShift).unwrap(),
            Value::from(0b10)
        );

        assert_eq!(
            Value::bitwise_op(l.clone(), Value::from(-1), BitwiseOperation::RightShift).unwrap(),
            Value::from(20)
        );

        assert_eq!(
            Value::bitwise_op(l.clone(), Value::from(64), BitwiseOperation::RightShift).unwrap(),
            Value::from(10)
        );

        assert_eq!(Value::bitwise_not(l.clone()).unwrap(), Value::from(-11));
        assert_eq!(
            Value::bitwise_not(Value::from(0u8)).unwrap(),
            Value::u8(255)
        );
        assert_eq!(Value::bitwise_not(Value::from(1)).unwrap(), Value::from(-2));

        assert_eq!(
            Value::bitwise_not(Value::from(0u8)).unwrap(),
            Value::from(u8::MAX)
        );
        assert_eq!(
            Value::bitwise_not(Value::from(0u16)).unwrap(),
            Value::from(u16::MAX)
        );
        assert_eq!(
            Value::bitwise_not(Value::from(0u32)).unwrap(),
            Value::from(u32::MAX)
        );
        assert_eq!(
            Value::bitwise_not(Value::from(0u64)).unwrap(),
            Value::from(u64::MAX)
        );
        assert_eq!(
            Value::bitwise_not(Value::from(0i8)).unwrap(),
            Value::from(-1_i8)
        );
        assert_eq!(
            Value::bitwise_not(Value::from(0i16)).unwrap(),
            Value::from(-1_i16)
        );
        assert_eq!(
            Value::bitwise_not(Value::from(I32::new(0))).unwrap(),
            Value::from(I32::new(-1))
        );
        assert_eq!(
            Value::bitwise_not(Value::from(I64::new(0))).unwrap(),
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
