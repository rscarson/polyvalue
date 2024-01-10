//! Object inner type
//!
//! This type is a wrapper around `BTreeMap<Value, Value>`.
//! It provides a way to store key-value pairs.
//!
use crate::{Error, Value, ValueType};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Inner type used for object storage
#[derive(PartialEq, Eq, Clone, Default, Debug, PartialOrd)]
pub struct ObjectInner(BTreeMap<Value, Value>);
impl ObjectInner {
    /// Create a new `ObjectInner`
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    /// Insert a key-value pair into the object, if the key is not a compound type
    pub fn insert(&mut self, key: Value, value: Value) -> Result<Option<Value>, Error> {
        if key.is_a(ValueType::Compound) {
            return Err(Error::InvalidTypeForKey(key.own_type()));
        }
        Ok(self.0.insert(key, value))
    }

    /// Remove a key-value pair from the object
    pub fn remove(&mut self, key: &Value) -> Option<Value> {
        self.0.remove(key)
    }

    /// Invokes the inner `BTreeMap`'s iterator
    pub fn iter(&self) -> impl Iterator<Item = (&Value, &Value)> {
        self.0.iter()
    }

    /// Invokes the inner `BTreeMap`'s mutable iterator
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Value, &mut Value)> {
        self.0.iter_mut()
    }

    /// Extends the inner `BTreeMap` with another
    pub fn extend(&mut self, other: ObjectInner) {
        self.0.extend(other.0);
    }

    /// The number of key-value pairs in the inner `BTreeMap`
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns true if the inner `BTreeMap` is empty
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Get a value from the object, if it exists
    pub fn get(&self, key: &Value) -> Option<&Value> {
        self.0.get(key)
    }

    /// Get a mutable value from the object, if it exists
    pub fn get_mut(&mut self, key: &Value) -> Option<&mut Value> {
        self.0.get_mut(key)
    }

    /// Get the keys from the inner `BTreeMap`
    pub fn keys(&self) -> impl Iterator<Item = &Value> {
        self.0.keys()
    }

    /// Get the values from the inner `BTreeMap`
    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.0.values()
    }

    /// Determine if the object contains a key
    pub fn contains_key(&self, key: &Value) -> bool {
        self.0.contains_key(key)
    }

    /// Get a mutable reference to the inner `BTreeMap`'s values
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut Value> {
        self.0.values_mut()
    }

    /// Retain only the key-value pairs that satisfy the predicate
    pub fn retain(&mut self, f: impl FnMut(&Value, &mut Value) -> bool) {
        self.0.retain(f)
    }
}

impl TryFrom<Vec<(Value, Value)>> for ObjectInner {
    type Error = Error;
    fn try_from(value: Vec<(Value, Value)>) -> Result<Self, Self::Error> {
        let mut map = Self::new();
        for (k, v) in value {
            map.insert(k, v)?;
        }
        Ok(map)
    }
}

impl<'de> Deserialize<'de> for ObjectInner {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let flat_map: Vec<(Value, Value)> = Deserialize::deserialize(deserializer)?;
        match Self::try_from(flat_map) {
            Ok(map) => Ok(map),
            Err(e) => Err(serde::de::Error::custom(e)),
        }
    }
}

impl Serialize for ObjectInner {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let flat_map: Vec<(Value, Value)> = self
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<Vec<(Value, Value)>>();
        flat_map.serialize(serializer)
    }
}
