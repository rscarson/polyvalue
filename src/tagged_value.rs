//! This module defines a tagged variant of Value, for use in serialization
//!
use crate::types::*;
use crate::InnerValue;
use crate::Value;
use serde::{Deserialize, Serialize};

pub type TaggedArray = Vec<TaggedValue>;

#[derive(PartialEq, Eq, Hash, Debug, Clone, PartialOrd, Ord)]
pub struct TaggedObject(std::collections::BTreeMap<TaggedValue, TaggedValue>);
impl<'de> Deserialize<'de> for TaggedObject {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let flat_map: Vec<(TaggedValue, TaggedValue)> = Deserialize::deserialize(deserializer)?;
        Ok(Self::from(flat_map))
    }
}

impl Serialize for TaggedObject {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let flat_map: Vec<(TaggedValue, TaggedValue)> = self
            .0
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<Vec<(TaggedValue, TaggedValue)>>();
        flat_map.serialize(serializer)
    }
}

impl From<Vec<(TaggedValue, TaggedValue)>> for TaggedObject {
    fn from(value: Vec<(TaggedValue, TaggedValue)>) -> Self {
        let mut map = TaggedObject(std::collections::BTreeMap::new());
        for (k, v) in value {
            map.0.insert(k, v);
        }
        map
    }
}

impl From<Object> for TaggedObject {
    fn from(value: Object) -> Self {
        let mut map = TaggedObject(std::collections::BTreeMap::new());
        for (k, v) in value.iter() {
            map.0.insert(k.clone().into(), v.clone().into());
        }
        map
    }
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Hash, Debug, Clone, PartialOrd, Ord)]
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
    Array(TaggedArray),
    Object(TaggedObject),
}

impl TaggedValue {
    pub fn serialize(&self) -> Result<serde_json::Value, serde_json::Error> {
        serde_json::to_value(self)
    }

    pub fn deserialize(value: &serde_json::Value) -> Result<Self, serde_json::Error> {
        serde_json::from_value(value.clone())
    }
}

impl From<TaggedValue> for Value {
    fn from(val: TaggedValue) -> Self {
        match val {
            TaggedValue::Bool(v) => Value::bool(v),
            TaggedValue::U8(v) => Value::u8(v),
            TaggedValue::I8(v) => Value::i8(v),
            TaggedValue::U16(v) => Value::u16(v),
            TaggedValue::I16(v) => Value::i16(v),
            TaggedValue::U32(v) => Value::u32(v),
            TaggedValue::I32(v) => Value::i32(v),
            TaggedValue::U64(v) => Value::u64(v),
            TaggedValue::I64(v) => Value::i64(v),
            TaggedValue::Float(v) => Value::float(v),
            TaggedValue::Fixed(v) => Value::fixed(v),
            TaggedValue::Currency(v) => Value::currency(v),
            TaggedValue::String(v) => Value::string(v),
            TaggedValue::Range(v) => Value::range(v),
            TaggedValue::Array(v) => {
                let array = v.into_iter().map(|v| v.into()).collect::<Vec<_>>();
                Value::array(array)
            }
            TaggedValue::Object(v) => {
                let object =
                    v.0.iter()
                        .map(|(k, v)| (k.clone().into(), v.clone().into()))
                        .collect::<Vec<(_, _)>>();
                let mut obj = ObjectInner::new();
                for (k, v) in object {
                    obj.insert(k, v).ok();
                }
                Value::object(obj)
            }
        }
    }
}

impl From<Value> for TaggedValue {
    fn from(value: Value) -> Self {
        match value.inner().clone() {
            InnerValue::Bool(v) => TaggedValue::Bool(v),
            InnerValue::U8(v) => TaggedValue::U8(v),
            InnerValue::I8(v) => TaggedValue::I8(v),
            InnerValue::U16(v) => TaggedValue::U16(v),
            InnerValue::I16(v) => TaggedValue::I16(v),
            InnerValue::U32(v) => TaggedValue::U32(v),
            InnerValue::I32(v) => TaggedValue::I32(v),
            InnerValue::U64(v) => TaggedValue::U64(v),
            InnerValue::I64(v) => TaggedValue::I64(v),
            InnerValue::Float(v) => TaggedValue::Float(v),
            InnerValue::Fixed(v) => TaggedValue::Fixed(v),
            InnerValue::Currency(v) => TaggedValue::Currency(v),
            InnerValue::String(v) => TaggedValue::String(v),
            InnerValue::Range(v) => TaggedValue::Range(v),
            InnerValue::Array(v) => {
                let tagged_array = v.iter().map(|v| v.clone().into()).collect();
                TaggedValue::Array(tagged_array)
            }
            InnerValue::Object(v) => TaggedValue::Object(v.into()),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::ValueTrait;

    use super::*;

    #[test]
    fn test_serialize() {
        let value = TaggedValue::Range((1..=2).into());
        let serialized = value.serialize().unwrap();
        let deserialized = TaggedValue::deserialize(&serialized).unwrap();
        assert_eq!(value, deserialized);

        let value = TaggedValue::Array(vec![
            TaggedValue::U8(1u8.into()),
            TaggedValue::U8(2u8.into()),
        ]);
        let serialized = value.serialize().unwrap();
        let deserialized = TaggedValue::deserialize(&serialized).unwrap();
        assert_eq!(serialized.to_string(), r#"{"Array":[{"U8":1},{"U8":2}]}"#);
        assert_eq!(value, deserialized);

        let mut object = TaggedObject(std::collections::BTreeMap::new());
        object
            .0
            .insert(TaggedValue::String("a".into()), TaggedValue::U8(1u8.into()));
        let value = TaggedValue::Object(object);
        let serialized = value.serialize().unwrap();
        let deserialized = TaggedValue::deserialize(&serialized).unwrap();
        assert_eq!(
            serialized.to_string(),
            r#"{"Object":[[{"String":"a"},{"U8":1}]]}"#
        );
        assert_eq!(value, deserialized);
    }

    #[test]
    fn test_from_value() {
        macro_rules! assert_from_value {
            ($primitive:expr, $variant:ident) => {
                assert!(matches!(
                    Value::from($primitive).into(),
                    TaggedValue::$variant(_)
                ));
            };
        }

        // Test that all crate::Value variants can be converted to TaggedValue
        assert_from_value!(true, Bool);
        assert_from_value!(1u8, U8);
        assert_from_value!(1i8, I8);
        assert_from_value!(1u16, U16);
        assert_from_value!(1i16, I16);
        assert_from_value!(1u32, U32);
        assert_from_value!(1i32, I32);
        assert_from_value!(1u64, U64);
        assert_from_value!(1i64, I64);
        assert_from_value!(1.0, Float);
        assert_from_value!(Fixed::one(), Fixed);
        assert_from_value!(CurrencyInner::from_fixed(Fixed::one()), Currency);
        assert_from_value!("a", String);
        assert_from_value!(1..=2, Range);
        assert_from_value!(vec![1.into(), 2.into()], Array);
        assert_from_value!(
            Object::new(ObjectInner::try_from(vec![(1.into(), 2.into())]).unwrap()),
            Object
        );
    }

    #[test]
    fn test_into_value() {
        macro_rules! assert_into_value {
            ($primitive:expr, $variant:ident) => {
                assert!(matches!(
                    Value::from(TaggedValue::$variant($primitive.into())).inner(),
                    InnerValue::$variant(_)
                ));
            };
        }

        // Test that all TaggedValue variants can be converted to crate::Value
        assert_into_value!(true, Bool);
        assert_into_value!(1u8, U8);
        assert_into_value!(1i8, I8);
        assert_into_value!(1u16, U16);
        assert_into_value!(1i16, I16);
        assert_into_value!(1u32, U32);
        assert_into_value!(1i32, I32);
        assert_into_value!(1u64, U64);
        assert_into_value!(1i64, I64);
        assert_into_value!(1.0, Float);
        assert_into_value!(Fixed::one(), Fixed);
        assert_into_value!(CurrencyInner::from_fixed(Fixed::one()), Currency);
        assert_into_value!("a", String);
        assert_into_value!(1..=2, Range);
        assert_into_value!(vec![TaggedValue::U8(1u8.into())], Array);
        assert_into_value!(
            Object::new(ObjectInner::try_from(vec![(1.into(), 2.into())]).unwrap()),
            Object
        );
    }
}
