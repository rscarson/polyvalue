//! This module defines the `ValueType` type, listing available types
//!
use crate::Error;
use serde::{Deserialize, Serialize};

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
        match s.to_lowercase().as_str() {
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

//
// Tests
//

#[cfg(test)]
mod test {
    use super::*;

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
        assert_eq!(ValueType::try_from("Bool").unwrap(), ValueType::Bool);
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
}
