use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Inner type used for object storage
pub type ObjectInner = HashMap<Value, Value>;

/// Subtype of `Value` that represents an object
#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Default)]
pub struct Object(ObjectInner);
impl_value!(Object, ObjectInner);

map_value!(
    from = Object,
    handle_into = |v: Object| Value::Object(v),
    handle_from = |v: Value| match v {
        Value::Object(v) => Ok(v),
        Value::Int(v) => v.try_into(),
        Value::Float(v) => v.try_into(),
        Value::Fixed(v) => v.try_into(),
        Value::Currency(v) => v.try_into(),
        Value::Bool(v) => v.try_into(),
        Value::String(v) => v.try_into(),
        Value::Array(v) => v.try_into(),
    }
);

//
// Trait implementations
//

impl Ord for Object {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd for Object {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let mut v1: Vec<(&Value, &Value)> = self.inner().iter().collect();
        let mut v2: Vec<(&Value, &Value)> = other.inner().iter().collect();
        v1.sort_by_key(|(k, _)| (*k).clone());
        v2.sort_by_key(|(k, _)| (*k).clone());
        Some(v1.cmp(&v2))
    }
}

impl std::hash::Hash for Object {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut v: Vec<(&Value, &Value)> = self.inner().iter().collect();
        v.sort_by_key(|(k, _)| (*k).clone());
        v.hash(state);
    }
}

impl ArithmeticOperationExt for Object {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        match operation {
            ArithmeticOperation::Add => {
                let mut result = left.clone();
                result.inner_mut().extend(right.inner().clone());
                Ok(result)
            }

            _ => Err(Error::UnsupportedOperation {
                operation: operation,
                actual_type: ValueType::Object,
            })?,
        }
    }
}

impl IndexingOperationExt for Object {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        self.inner().get(index).cloned().ok_or(Error::Index {
            key: index.to_string(),
        })
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        self.inner_mut().insert(index.clone(), value);
        Ok(())
    }
}

//
// Conversion from other types
//

macro_rules! into_singleton {
    ($type:ident) => {
        map_type!(into = $type, from = Object, |v: Object| {
            if v.inner().len() == 1 {
                let first = v.inner().values().next().unwrap().clone();
                first.try_into()
            } else {
                Err(crate::Error::ValueConversion {
                    src_type: ValueType::Object,
                    dst_type: ValueType::$type,
                })
            }
        });
    };
}

map_type!(into = Bool, from = Object, |v: Object| {
    Ok((v.inner().len() != 0).into())
});

into_singleton!(Fixed);
into_singleton!(Float);
into_singleton!(Int);
into_singleton!(Currency);

map_type!(into = Str, from = Object, |v: Object| {
    Ok(format!(
        "{{{}}}",
        v.inner()
            .iter()
            .map(|v| format!("{}:{}", v.0, v.1))
            .collect::<Vec<String>>()
            .join(", ")
    )
    .into())
});

map_type!(into = Array, from = Object, |v: Object| {
    Ok(v.inner().values().cloned().collect::<Vec<Value>>().into())
});
