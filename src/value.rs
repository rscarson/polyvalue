//! This module defines the `Value` type, and the `ValueTrait` trait.
//! The `Value` type is an enum that can hold any of the supported value types.
//!
use crate::operations::*;
use crate::types::*;
use crate::Error;
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
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub enum ValueType {
    /// A boolean value
    Bool,

    /// A fixed-point value
    Fixed,

    /// A floating-point value
    Float,

    /// A currency value
    Currency,

    /// An unsigned 8bit integer value
    U8,

    /// An unsigned 16bit integer value
    U16,

    /// An unsigned 32bit integer value
    U32,

    /// An unsigned 64bit integer value
    U64,

    /// A signed 8bit integer value
    I8,

    /// A signed 16bit integer value
    I16,

    /// A signed 32bit integer value
    I32,

    /// A signed 64bit integer value
    I64,

    /// An integer value
    Int,

    /// A string value
    String,

    /// A range value
    Range,

    /// An array value
    Array,

    /// An object value
    Object,

    /// A numeric value (fixed, float, currency, or int)
    Numeric,

    /// A compound value (array, range or object)
    Compound,

    /// Any value
    Any,
}

impl Serialize for ValueType {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.to_string().as_str())
    }
}

impl<'de> Deserialize<'de> for ValueType {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        ValueType::try_from(s.as_str()).map_err(serde::de::Error::custom)
    }
}

impl std::fmt::Display for ValueType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueType::Bool => write!(f, "bool"),
            ValueType::Fixed => write!(f, "fixed"),
            ValueType::Float => write!(f, "float"),
            ValueType::Currency => write!(f, "currency"),
            ValueType::U8 => write!(f, "u8"),
            ValueType::U16 => write!(f, "u16"),
            ValueType::U32 => write!(f, "u32"),
            ValueType::U64 => write!(f, "u64"),
            ValueType::I8 => write!(f, "i8"),
            ValueType::I16 => write!(f, "i16"),
            ValueType::I32 => write!(f, "i32"),
            ValueType::I64 => write!(f, "i64"),
            ValueType::Int => write!(f, "int"),
            ValueType::String => write!(f, "string"),
            ValueType::Range => write!(f, "range"),
            ValueType::Array => write!(f, "array"),
            ValueType::Object => write!(f, "object"),
            ValueType::Numeric => write!(f, "numeric"),
            ValueType::Compound => write!(f, "compound"),
            ValueType::Any => write!(f, "any"),
        }
    }
}

impl TryFrom<&str> for ValueType {
    type Error = Error;
    fn try_from(s: &str) -> Result<Self, Error> {
        match s {
            "bool" => Ok(ValueType::Bool),
            "fixed" => Ok(ValueType::Fixed),
            "float" => Ok(ValueType::Float),
            "currency" => Ok(ValueType::Currency),
            "u8" => Ok(ValueType::U8),
            "u16" => Ok(ValueType::U16),
            "u32" => Ok(ValueType::U32),
            "u64" => Ok(ValueType::U64),
            "i8" => Ok(ValueType::I8),
            "i16" => Ok(ValueType::I16),
            "i32" => Ok(ValueType::I32),
            "i64" => Ok(ValueType::I64),
            "int" => Ok(ValueType::Int),
            "string" => Ok(ValueType::String),
            "range" => Ok(ValueType::Range),
            "array" => Ok(ValueType::Array),
            "object" => Ok(ValueType::Object),
            "numeric" => Ok(ValueType::Numeric),
            "compound" => Ok(ValueType::Compound),
            "any" => Ok(ValueType::Any),
            _ => Err(Error::UnrecognizedType(s.to_string())),
        }
    }
}

/// Main value type
/// This is an enum that can hold any of the supported value types
#[derive(Clone, Serialize, Deserialize, Debug, Eq, Hash, PartialEq)]
#[serde(untagged)]
pub enum Value {
    /// A boolean value
    Bool(Bool),

    /// An integer value
    Int(Int),

    /// An unsigned 8bit integer value
    U8(U8),

    /// An unsigned 16bit integer value
    U16(U16),

    /// An unsigned 32bit integer value
    U32(U32),

    /// An unsigned 64bit integer value
    U64(U64),

    /// An unsigned 8bit integer value
    I8(I8),

    /// An signed 16bit integer value
    I16(I16),

    /// An signed 32bit integer value
    I32(I32),

    /// An signed 64bit integer value
    I64(I64),

    /// A floating-point value
    Float(Float),

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

            ValueType::Numeric => {
                return Err(Error::ValueConversion {
                    src_type: self.own_type(),
                    dst_type: ValueType::Numeric,
                })
            }

            ValueType::Compound => {
                return Err(Error::ValueConversion {
                    src_type: self.own_type(),
                    dst_type: ValueType::Compound,
                })
            }

            ValueType::Any => {
                return Err(Error::ValueConversion {
                    src_type: self.own_type(),
                    dst_type: ValueType::Any,
                })
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
            Value::Int(_) => ValueType::Int,
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
            ValueType::Numeric => Int::try_from(self.clone()).is_ok(),
            ValueType::Compound => {
                self.own_type() == ValueType::Array
                    || self.own_type() == ValueType::Object
                    || self.own_type() == ValueType::Range
                    || self.own_type() == ValueType::String
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

            ValueType::Int => Int::try_from(self.clone())?.into(),
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
                (ValueType::Range, _) | (_, ValueType::Range) => ValueType::Range,
                (ValueType::Object, _) | (_, ValueType::Object) => ValueType::Object,
                (ValueType::Array, _) | (_, ValueType::Array) => ValueType::Array,
                (ValueType::String, _) | (_, ValueType::String) => ValueType::String,

                (ValueType::Currency, _) | (_, ValueType::Currency) => ValueType::Currency,
                (ValueType::Fixed, _) | (_, ValueType::Fixed) => ValueType::Fixed,
                (ValueType::Float, _) | (_, ValueType::Float) => ValueType::Float,
                (ValueType::Int, _) | (_, ValueType::Int) => ValueType::Int,

                (ValueType::I64, _) | (_, ValueType::I64) => ValueType::I64,
                (ValueType::U64, _) | (_, ValueType::U64) => ValueType::U64,
                (ValueType::I32, _) | (_, ValueType::I32) => ValueType::I32,
                (ValueType::U32, _) | (_, ValueType::U32) => ValueType::U32,
                (ValueType::I16, _) | (_, ValueType::I16) => ValueType::I16,
                (ValueType::U16, _) | (_, ValueType::U16) => ValueType::U16,
                (ValueType::I8, _) | (_, ValueType::I8) => ValueType::I8,
                (ValueType::U8, _) | (_, ValueType::U8) => ValueType::U8,

                (ValueType::Bool, _) | (_, ValueType::Bool) => ValueType::Bool,

                (ValueType::Numeric, _) | (_, ValueType::Numeric) => ValueType::Numeric,
                (ValueType::Compound, _) | (_, ValueType::Compound) => ValueType::Compound,
                (ValueType::Any, _) => ValueType::Any,
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
            ValueType::Int => Int::cmp(&l.as_a::<Int>().unwrap(), &r.as_a::<Int>().unwrap()),

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

            ValueType::Numeric => {
                return Err(Error::ValueConversion {
                    src_type: self.own_type(),
                    dst_type: ValueType::Numeric,
                })
            }

            ValueType::Compound => {
                return Err(Error::ValueConversion {
                    src_type: self.own_type(),
                    dst_type: ValueType::Compound,
                })
            }

            ValueType::Any => {
                return Err(Error::ValueConversion {
                    src_type: self.own_type(),
                    dst_type: ValueType::Any,
                })
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

            Value::Int(v) => write!(f, "{}", v),
            Value::String(v) => write!(f, "{}", v),
            Value::Range(v) => write!(f, "{}", v),
            Value::Array(v) => write!(f, "{}", v),
            Value::Object(v) => write!(f, "{}", v),
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

                (Value::Int(_), _) => Some(std::cmp::Ordering::Less),
                (_, Value::Int(_)) => Some(std::cmp::Ordering::Greater),

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

                (Value::Object(_), _) => Some(std::cmp::Ordering::Greater),
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
            if self.either_type(other, ValueType::Range) {
                if other.is_a(ValueType::Compound) {
                    return std::cmp::Ordering::Less;
                } else {
                    return std::cmp::Ordering::Greater;
                }
            }

            // We should in theory never get here
            // Anything here is a bug in resolution order logic
            panic!("Could not compare values {:?} and {:?}", self, other);
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
            (Value::I64(l), Value::I64(r)) => I64::bitwise_op(&l, &r, operation).map(Into::into),

            _ => {
                let left = left.as_a::<Int>()?;
                let right = right.as_a::<Int>()?;
                Int::bitwise_op(&left, &right, operation).map(Into::into)
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

            (Value::Int(l), Value::Int(r)) => Int::arithmetic_op(&l, &r, operation).map(Into::into),

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
            ValueType::Int => Int::is_operator_supported(
                &self.as_a::<Int>().unwrap(),
                &other.as_a::<Int>().unwrap(),
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

            ValueType::Numeric | ValueType::Compound | ValueType::Any => false,
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
    use std::{cmp::Ordering, vec};

    use super::*;
    use fpdec::Decimal;

    #[test]
    fn test_valuetype() {
        // serialize / deserialize valuetype
        let serialized = serde_json::to_string(&ValueType::Bool).unwrap();
        let deserialized: ValueType = serde_json::from_str(&serialized).unwrap();
        assert_eq!(deserialized, ValueType::Bool);

        // display
        assert_eq!(format!("{}", ValueType::Bool), "bool");
        assert_eq!(format!("{}", ValueType::Fixed), "fixed");
        assert_eq!(format!("{}", ValueType::Float), "float");
        assert_eq!(format!("{}", ValueType::Currency), "currency");
        assert_eq!(format!("{}", ValueType::Int), "int");
        assert_eq!(format!("{}", ValueType::String), "string");
        assert_eq!(format!("{}", ValueType::Array), "array");
        assert_eq!(format!("{}", ValueType::Object), "object");
        assert_eq!(format!("{}", ValueType::Range), "range");
        assert_eq!(format!("{}", ValueType::Compound), "compound");
        assert_eq!(format!("{}", ValueType::Numeric), "numeric");
        assert_eq!(format!("{}", ValueType::Any), "any");
        assert_eq!(format!("{}", ValueType::U8), "u8");
        assert_eq!(format!("{}", ValueType::U16), "u16");
        assert_eq!(format!("{}", ValueType::U32), "u32");
        assert_eq!(format!("{}", ValueType::U64), "u64");
        assert_eq!(format!("{}", ValueType::I8), "i8");
        assert_eq!(format!("{}", ValueType::I16), "i16");
        assert_eq!(format!("{}", ValueType::I32), "i32");
        assert_eq!(format!("{}", ValueType::I64), "i64");

        // try_from str
        assert_eq!(ValueType::try_from("bool").unwrap(), ValueType::Bool);
        assert_eq!(ValueType::try_from("fixed").unwrap(), ValueType::Fixed);
        assert_eq!(ValueType::try_from("float").unwrap(), ValueType::Float);
        assert_eq!(
            ValueType::try_from("currency").unwrap(),
            ValueType::Currency
        );
        assert_eq!(ValueType::try_from("int").unwrap(), ValueType::Int);
        assert_eq!(ValueType::try_from("string").unwrap(), ValueType::String);
        assert_eq!(ValueType::try_from("array").unwrap(), ValueType::Array);
        assert_eq!(ValueType::try_from("object").unwrap(), ValueType::Object);
        assert_eq!(ValueType::try_from("range").unwrap(), ValueType::Range);
        assert_eq!(
            ValueType::try_from("compound").unwrap(),
            ValueType::Compound
        );
        assert_eq!(ValueType::try_from("numeric").unwrap(), ValueType::Numeric);
        assert_eq!(ValueType::try_from("any").unwrap(), ValueType::Any);
        ValueType::try_from("poo").unwrap_err();
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
            Some(&Value::from(1))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("string")),
            Some(&Value::from("abc"))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("array")),
            Some(&Value::from(vec![
                Value::from(1),
                Value::from(2),
                Value::from(3)
            ]))
        );
        assert_eq!(
            value.as_a::<Object>().unwrap().get(&Value::from("range")),
            Some(&Value::from(vec![
                Value::from(1),
                Value::from(2),
                Value::from(3)
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

        let a = Value::from(Decimal::ZERO);
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
            .as_a::<Int>()
            .expect("Value could not be converted to int!");
        assert_eq!(int, Int::from(1i64));

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
            Object::try_from(vec![(Value::from(0), Value::from(1.0))]).unwrap()
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
        assert!(Value::from(Decimal::ZERO).is_a(ValueType::Numeric));
        assert!(
            Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO)))
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
            Value::try_from(vec![(Value::from(0), Value::from(1.0))]).unwrap()
        );

        let value = Value::from(1.0);
        let value = value
            .as_type(ValueType::Any)
            .expect("Value could not be converted to any!");
        assert_eq!(value, Value::from(1.0));

        let value = Value::from(1);
        assert_eq!(value.as_type(ValueType::Numeric).unwrap(), Value::from(1));

        let value = Value::from(1.0);
        assert_eq!(value.as_type(ValueType::Numeric).unwrap(), Value::from(1.0));

        let value = Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO)));
        assert_eq!(
            value.as_type(ValueType::Numeric).unwrap(),
            Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO)))
        );

        let value = Value::from(Decimal::ZERO);
        assert_eq!(
            value.as_type(ValueType::Numeric).unwrap(),
            Value::from(Fixed::from(Decimal::ZERO))
        );

        assert_eq!(
            Value::from(1).as_type(ValueType::Bool).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Value::from(0).as_type(ValueType::Fixed).unwrap(),
            Value::from(Fixed::from(Decimal::ZERO))
        );

        assert_eq!(
            Value::from(0).as_type(ValueType::Currency).unwrap(),
            Value::from(CurrencyInner::from_fixed(Fixed::from(Decimal::ZERO)))
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
            Value::try_from(vec![(Value::from(0), Value::from(1))]).unwrap()
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

        // u8/u16 = u16
        let a = Value::from(1u8);
        let b = Value::from(1u16);
        assert_eq!(a.type_for_comparison(&b), ValueType::U16);

        // u8/u32 = u32
        let a = Value::from(1u8);
        let b = Value::from(1u32);
        assert_eq!(a.type_for_comparison(&b), ValueType::U32);

        // u8/u64 = u64
        let a = Value::from(1u8);
        let b = Value::from(1u64);
        assert_eq!(a.type_for_comparison(&b), ValueType::U64);

        // u8/i8 = i8
        let a = Value::from(1u8);
        let b = Value::from(1i8);
        assert_eq!(a.type_for_comparison(&b), ValueType::I8);

        // u8/i16 = i16
        let a = Value::from(1u8);
        let b = Value::from(1i16);
        assert_eq!(a.type_for_comparison(&b), ValueType::I16);

        // u8/i32 = i32
        let a = Value::from(1u8);
        let b = Value::from(I32::new(1));
        assert_eq!(a.type_for_comparison(&b), ValueType::I32);

        // u8/i64 = i64
        let a = Value::from(1u8);
        let b = Value::from(I64::new(1));
        assert_eq!(a.type_for_comparison(&b), ValueType::I64);

        // u8/bool = u8
        let a = Value::from(1u8);
        let b = Value::from(true);
        assert_eq!(a.type_for_comparison(&b), ValueType::U8);

        // bool / bool = bool
        let a = Value::from(true);
        let b = Value::from(false);
        assert_eq!(a.type_for_comparison(&b), ValueType::Bool);
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

        assert_eq!(Value::from(1u8).cmp(&Value::from(true)), Ordering::Greater);
        assert_eq!(Value::from(true).cmp(&Value::from(1u8)), Ordering::Less);

        assert_eq!(Value::from(1i8).cmp(&Value::from(1u8)), Ordering::Greater);
        assert_eq!(Value::from(1u8).cmp(&Value::from(1i8)), Ordering::Less);

        assert_eq!(Value::from(1i8).cmp(&Value::from(1i16)), Ordering::Less);
        assert_eq!(Value::from(1i16).cmp(&Value::from(1i8)), Ordering::Greater);

        assert_eq!(Value::from(1u16).cmp(&Value::from(1i16)), Ordering::Less);
        assert_eq!(Value::from(1i16).cmp(&Value::from(1)), Ordering::Less);
        assert_eq!(Value::from(1).cmp(&Value::from(1i16)), Ordering::Greater);

        assert_eq!(Value::from(1i32).cmp(&Value::from(1u32)), Ordering::Greater);
        assert_eq!(Value::from(1u32).cmp(&Value::from(1)), Ordering::Less);

        // bool, then u8, i8... etc
        assert_eq!(Value::from(true).cmp(&Value::from(true)), Ordering::Equal);
        assert_eq!(Value::from(1u8).cmp(&Value::from(1u8)), Ordering::Equal);
        assert_eq!(Value::from(1i8).cmp(&Value::from(1i8)), Ordering::Equal);
        assert_eq!(Value::from(1u16).cmp(&Value::from(1u16)), Ordering::Equal);
        assert_eq!(Value::from(1i16).cmp(&Value::from(1i16)), Ordering::Equal);
        assert_eq!(Value::from(1u32).cmp(&Value::from(1u32)), Ordering::Equal);
        assert_eq!(
            Value::from(I32::new(1)).cmp(&Value::from(I32::new(1))),
            Ordering::Equal
        );
        assert_eq!(
            Value::from(I64::new(1)).cmp(&Value::from(I64::new(1))),
            Ordering::Equal
        );
        assert_eq!(Value::from(1i64).cmp(&Value::from(1i64)), Ordering::Equal);
        assert_eq!(Value::from(1).cmp(&Value::from(1)), Ordering::Equal);
        assert_eq!(Value::from(1.0).cmp(&Value::from(1.0)), Ordering::Equal);
        assert_eq!(
            Value::from(Decimal::ZERO).cmp(&Value::from(Decimal::ZERO)),
            Ordering::Equal
        );
        assert_eq!(
            Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO))).cmp(&Value::from(
                CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO))
            )),
            Ordering::Equal
        );
        assert_eq!(Value::from("a").cmp(&Value::from("a")), Ordering::Equal);
        assert_eq!(
            Value::from(0..=10).cmp(&Value::from(0..=10)),
            Ordering::Equal
        );
        assert_eq!(
            Value::from(vec![Value::from(1)]).cmp(&Value::from(vec![Value::from(1)])),
            Ordering::Equal
        );
        assert_eq!(
            Value::try_from(vec![(Value::from("a"), Value::from(1))])
                .unwrap()
                .cmp(&Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap()),
            Ordering::Equal
        );

        // Bool to all
        assert_eq!(Value::from(true).cmp(&Value::from(1u8)), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(0u8)), Ordering::Greater);
        assert_eq!(Value::from(true).cmp(&Value::from(1i8)), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(1u16)), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(1i16)), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(1u32)), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(1i32)), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(1u64)), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(1i64)), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(1)), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(1.0)), Ordering::Less);
        assert_eq!(
            Value::from(true).cmp(&Value::from(Decimal::ONE)),
            Ordering::Less
        );
        assert_eq!(
            Value::from(true).cmp(&Value::from(CurrencyInner::as_dollars(Fixed::from(
                Decimal::ONE
            )))),
            Ordering::Less
        );
        assert_eq!(Value::from(true).cmp(&Value::from("true")), Ordering::Less);
        assert_eq!(Value::from(true).cmp(&Value::from(0..=10)), Ordering::Less);
        assert_eq!(
            Value::from(true).cmp(&Value::from(vec![Value::from(1)])),
            Ordering::Less
        );
        assert_eq!(
            Value::from(true)
                .cmp(&Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap()),
            Ordering::Less
        );
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
        Value::arithmetic_neg(&Value::from(Decimal::ZERO)).unwrap();
        Value::arithmetic_neg(&Value::from(CurrencyInner::as_dollars(Fixed::from(
            Decimal::ZERO,
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
            Value::from(Decimal::ZERO)
                .is_operator_supported(&Value::from(Decimal::ZERO), ArithmeticOperation::Add)
        );
        assert_eq!(
            true,
            Value::from(CurrencyInner::as_dollars(Fixed::from(Decimal::ZERO)))
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
        assert_eq!(v, Value::from(2));

        // Get indices on range
        let range = Value::from(Range::from(1..=3));
        let v = range
            .get_indices(&Value::from(vec![Value::from(0), Value::from(1)]))
            .unwrap();
        assert_eq!(v, Value::from(vec![Value::from(1), Value::from(2)]));

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

        assert_eq!(
            Value::bitwise_op(&l, &r, BitwiseOperation::Not).unwrap(),
            Value::from(0b0101)
        );

        assert_eq!(
            Value::bitwise_op(&Value::from(0), &r, BitwiseOperation::Not).unwrap(),
            Value::from(1)
        );

        assert_eq!(
            Value::bitwise_op(&Value::from(1), &r, BitwiseOperation::Not).unwrap(),
            Value::from(0)
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
