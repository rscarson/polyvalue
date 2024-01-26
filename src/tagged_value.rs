//! This module defines a tagged variant of Value, for use in serialization
//!
use crate::types::*;
use crate::Value;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub enum TaggedValue {
    /// A boolean value
    Bool(Bool),
    U8(U8),
    I8(I8),
    U16(U16),
    I16(I16),
    U32(U32),
    I32(I32),
    U64(U64),
    I64(I64),
    Float(Float),
    Fixed(Fixed),
    Currency(Currency),
    String(Str),
    Range(Range),
    Array(Array),
    Object(Object),
}

impl Into<Value> for TaggedValue {
    fn into(self) -> Value {
        match self {
            TaggedValue::Bool(v) => Value::Bool(v),
            TaggedValue::U8(v) => Value::U8(v),
            TaggedValue::I8(v) => Value::I8(v),
            TaggedValue::U16(v) => Value::U16(v),
            TaggedValue::I16(v) => Value::I16(v),
            TaggedValue::U32(v) => Value::U32(v),
            TaggedValue::I32(v) => Value::I32(v),
            TaggedValue::U64(v) => Value::U64(v),
            TaggedValue::I64(v) => Value::I64(v),
            TaggedValue::Float(v) => Value::Float(v),
            TaggedValue::Fixed(v) => Value::Fixed(v),
            TaggedValue::Currency(v) => Value::Currency(v),
            TaggedValue::String(v) => Value::String(v),
            TaggedValue::Range(v) => Value::Range(v),
            TaggedValue::Array(v) => Value::Array(v),
            TaggedValue::Object(v) => Value::Object(v),
        }
    }
}

impl From<Value> for TaggedValue {
    fn from(value: Value) -> Self {
        match value {
            Value::Bool(v) => TaggedValue::Bool(v),
            Value::U8(v) => TaggedValue::U8(v),
            Value::I8(v) => TaggedValue::I8(v),
            Value::U16(v) => TaggedValue::U16(v),
            Value::I16(v) => TaggedValue::I16(v),
            Value::U32(v) => TaggedValue::U32(v),
            Value::I32(v) => TaggedValue::I32(v),
            Value::U64(v) => TaggedValue::U64(v),
            Value::I64(v) => TaggedValue::I64(v),
            Value::Float(v) => TaggedValue::Float(v),
            Value::Fixed(v) => TaggedValue::Fixed(v),
            Value::Currency(v) => TaggedValue::Currency(v),
            Value::String(v) => TaggedValue::String(v),
            Value::Range(v) => TaggedValue::Range(v),
            Value::Array(v) => TaggedValue::Array(v),
            Value::Object(v) => TaggedValue::Object(v),
        }
    }
}
