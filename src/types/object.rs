use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Inner type used for object storage
pub type ObjectInner = BTreeMap<Value, Value>;

/// Subtype of `Value` that represents an object
#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Default, Debug)]
pub struct Object(ObjectInner);
impl_value!(Object, ObjectInner, |v: &Self| {
    format!(
        "{{{}}}",
        v.inner()
            .iter()
            .map(|(k, v)| format!("{}: {}", k.to_string(), v.to_string()))
            .collect::<Vec<String>>()
            .join(", ")
    )
});

map_value!(
    from = Object,
    handle_into = |v: Object| Value::Object(v),
    handle_from = |v: Value| match v {
        Value::Object(v) => Ok(v),
        Value::Int(v) => {
            let mut map = ObjectInner::new();
            map.insert(Value::Int(Int::from(0)), Value::Int(v));
            Ok(Object(map))
        }
        Value::Float(v) => {
            let mut map = ObjectInner::new();
            map.insert(Value::Int(0.into()), Value::Float(v));
            Ok(Object(map))
        }
        Value::Fixed(v) => {
            let mut map = ObjectInner::new();
            map.insert(Value::Int(0.into()), Value::Fixed(v));
            Ok(Object(map))
        }
        Value::Currency(v) => {
            let mut map = ObjectInner::new();
            map.insert(Value::Int(0.into()), Value::Currency(v));
            Ok(Object(map))
        }
        Value::Bool(v) => {
            let mut map = ObjectInner::new();
            map.insert(Value::Int(0.into()), Value::Bool(v));
            Ok(Object(map))
        }
        Value::String(v) => {
            let mut map = ObjectInner::new();
            map.insert(Value::Int(0.into()), Value::String(v));
            Ok(Object(map))
        }
        Value::Array(v) => {
            let mut map = ObjectInner::new();
            for (i, v) in v.inner().iter().enumerate() {
                map.insert(Value::Int((i as i64).into()), v.clone());
            }
            Ok(Object(map))
        }
    }
);

map_type!(Bool, Object);
map_type!(Int, Object);
map_type!(Float, Object);
map_type!(Fixed, Object);
map_type!(Currency, Object);
map_type!(Str, Object);
map_type!(Array, Object);

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
    fn get_index(&self, index: &Value) -> Result<&Value, crate::Error> {
        self.inner().get(index).ok_or(Error::Index {
            key: index.to_string(),
        })
    }

    fn get_index_mut(&mut self, index: &Value) -> Result<&mut Value, crate::Error> {
        self.inner_mut().get_mut(index).ok_or(Error::Index {
            key: index.to_string(),
        })
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        self.inner_mut().insert(index.clone(), value);
        Ok(())
    }
}
