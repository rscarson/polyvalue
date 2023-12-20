//! Object type
//!
//! This type is a wrapper around `BTreeMap<Value, Value>`.
//! It provides a way to store key-value pairs.
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `{<key>: <value>, <key>: <value>, ...}`
//!
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

impl From<Vec<(Value, Value)>> for Object {
    fn from(value: Vec<(Value, Value)>) -> Self {
        let mut map = ObjectInner::new();
        for (k, v) in value {
            map.insert(k, v);
        }
        Object(map)
    }
}

impl Object {
    /// Insert a key-value pair into the object
    /// If the key already exists, it will be overwritten
    pub fn insert(&mut self, key: Value, value: Value) {
        self.inner_mut().insert(key, value);
    }

    /// Remove a key-value pair from the object
    /// Returns the value if it existed
    pub fn remove(&mut self, key: &Value) -> Option<Value> {
        self.inner_mut().remove(key)
    }

    /// Get a value from the object, if it exists
    pub fn get(&self, key: &Value) -> Option<&Value> {
        self.inner().get(key)
    }

    /// Get a mutable value from the object, if it exists
    pub fn get_mut(&mut self, key: &Value) -> Option<&mut Value> {
        self.inner_mut().get_mut(key)
    }

    /// Determine if the object contains any values
    pub fn is_empty(&self) -> bool {
        self.inner().is_empty()
    }

    /// Get a list of all keys in the object
    pub fn keys(&self) -> Vec<&Value> {
        self.inner().keys().collect()
    }

    /// Get a list of all values in the object
    pub fn values(&self) -> Vec<&Value> {
        self.inner().values().collect()
    }
}

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

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Object::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }
}

impl BooleanOperationExt for Object {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => !left.inner().is_empty() && !right.inner().is_empty(),
            BooleanOperation::Or => !left.inner().is_empty() || !right.inner().is_empty(),

            BooleanOperation::LT => *left.inner() < *right.inner(),
            BooleanOperation::GT => *left.inner() > *right.inner(),
            BooleanOperation::LTE => *left.inner() <= *right.inner(),
            BooleanOperation::GTE => *left.inner() >= *right.inner(),
            BooleanOperation::EQ => *left.inner() == *right.inner(),
            BooleanOperation::NEQ => *left.inner() != *right.inner(),
            BooleanOperation::Not => left.inner().is_empty(),
        };

        Ok(result.into())
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Object::boolean_op(self, &self.clone(), BooleanOperation::Not)
    }
}

impl IndexingOperationExt for Object {
    fn get_index(&self, index: &Value) -> Result<&Value, crate::Error> {
        self.get(index).ok_or(Error::Index {
            key: index.to_string(),
        })
    }

    fn get_indices(&self, index: &Value) -> Result<Vec<&Value>, Error> {
        let indices = index.as_a::<Array>()?;
        indices
            .inner()
            .iter()
            .map(|i| self.get_index(i))
            .collect::<Result<Vec<_>, Error>>()
    }

    fn get_index_mut(&mut self, index: &Value) -> Result<&mut Value, crate::Error> {
        self.get_mut(index).ok_or(Error::Index {
            key: index.to_string(),
        })
    }

    fn get_indices_mut(&mut self, index: &Value) -> Result<Vec<&mut Value>, crate::Error> {
        let indices = index.as_a::<Array>()?.inner().clone();
        self.inner_mut()
            .iter_mut()
            .filter(|(k, _)| indices.contains(k))
            .map(|(_, v)| Ok(v))
            .collect::<Result<Vec<_>, Error>>()
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        self.inner_mut().insert(index.clone(), value);
        Ok(())
    }
}
