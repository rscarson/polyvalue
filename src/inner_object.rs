//! Object inner type
//!
//! This type is a wrapper around `HashMap<Value, Value>`.
//! It provides a way to store key-value pairs.
//!
use crate::{Error, Value, ValueType};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Inner type used for object storage
#[derive(PartialEq, Eq, Clone, Default, Debug)]
pub struct ObjectInner(HashMap<Value, Value>);
impl ObjectInner {
    /// Create a new `ObjectInner`
    pub fn new() -> Self {
        Self(HashMap::new())
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

    /// Invokes the inner `HashMap`'s iterator
    pub fn iter(&self) -> impl Iterator<Item = (&Value, &Value)> {
        self.0.iter()
    }

    /// Invokes the inner `HashMap`'s mutable iterator
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Value, &mut Value)> {
        self.0.iter_mut()
    }

    /// Extends the inner `HashMap` with another
    pub fn extend(&mut self, other: ObjectInner) {
        self.0.extend(other.0);
    }

    /// The number of key-value pairs in the inner `HashMap`
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns true if the inner `HashMap` is empty
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

    /// Get the keys from the inner `HashMap`
    pub fn keys(&self) -> impl Iterator<Item = &Value> {
        self.0.keys()
    }

    /// Get the values from the inner `HashMap`
    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.0.values()
    }

    /// Determine if the object contains a key
    pub fn contains_key(&self, key: &Value) -> bool {
        self.0.contains_key(key)
    }

    /// Get a mutable reference to the inner `HashMap`'s values
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

impl std::hash::Hash for ObjectInner {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut v: Vec<(&Value, &Value)> = self.0.iter().collect();
        v.sort_by_key(|(k, _)| *k);
        v.hash(state);
    }
}

impl PartialOrd for ObjectInner {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        println!("!");
        let mut v1: Vec<(&Value, &Value)> = self.0.iter().collect();
        let mut v2: Vec<(&Value, &Value)> = other.0.iter().collect();
        v1.sort_by_key(|(k, _)| *k);
        v2.sort_by_key(|(k, _)| *k);
        v1.partial_cmp(&v2)
    }
}

impl Ord for ObjectInner {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[cfg(test)]
mod test {
    use std::hash::Hash;

    use super::*;
    use fpdec::Decimal;

    fn get_hash(obj: &ObjectInner) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        obj.hash(&mut hasher);
        std::hash::Hasher::finish(&hasher)
    }

    #[test]
    fn test_hashing() {
        let mut obj = ObjectInner::new();
        obj.insert(Value::from(false), Value::from(0)).unwrap();
        obj.insert(Value::from(0), Value::from(1)).unwrap();
        obj.insert(Value::from(0.0), Value::from(2)).unwrap();
        obj.insert(Value::from(Decimal::ZERO), Value::from(3))
            .unwrap();
        obj.insert(Value::from("".to_string()), Value::from(4))
            .unwrap();

        assert_ne!(Value::from(false), Value::from(0));
        assert_ne!(Value::from(0), Value::from(0.0));
        assert_ne!(Value::from(0.0), Value::from(Decimal::ZERO));
        assert_ne!(Value::from(Decimal::ZERO), Value::from("".to_string()));

        assert_eq!(obj.get(&Value::from(false)), Some(&Value::from(0)));
        assert_eq!(obj.get(&Value::from(0)), Some(&Value::from(1)));
        assert_eq!(obj.get(&Value::from(0.0)), Some(&Value::from(2)));
        assert_eq!(obj.get(&Value::from(Decimal::ZERO)), Some(&Value::from(3)));
        assert_eq!(obj.get(&Value::from("".to_string())), Some(&Value::from(4)));
        assert_eq!(5, obj.len());

        assert_eq!(get_hash(&obj), get_hash(&obj));

        let mut obj2 = obj.clone();
        assert_eq!(get_hash(&obj), get_hash(&obj2));

        obj2.remove(&Value::from(false));
        assert_ne!(get_hash(&obj), get_hash(&obj2));
    }

    #[test]
    fn test_bad_key() {
        let mut obj = ObjectInner::new();
        assert!(obj
            .insert(Value::from(vec![Value::from(1)]), Value::from(0))
            .is_err());
        assert!(obj
            .insert(
                Value::try_from(vec![(Value::from(1), Value::from(2))]).unwrap(),
                Value::from(0)
            )
            .is_err());
        assert!(obj.insert(Value::from(0..=1), Value::from(0)).is_err());

        assert!(obj
            .insert(Value::from(0), Value::from(vec![Value::from(1)]))
            .is_ok());

        assert_eq!(1, obj.keys().count());
        assert!(obj.contains_key(&Value::from(0)));
        assert_eq!(
            obj.values_mut().collect::<Vec<_>>(),
            vec![&mut Value::from(vec![Value::from(1)])]
        );

        assert_eq!(
            obj.remove(&Value::from(0)).unwrap(),
            Value::from(vec![Value::from(1)])
        );
    }

    #[test]
    fn test_serialize() {
        let mut obj = ObjectInner::new();
        obj.insert(Value::from(false), Value::from(0)).unwrap();
        obj.insert(Value::from(0), Value::from(1)).unwrap();
        obj.insert(Value::from(0.0), Value::from(2)).unwrap();
        obj.insert(Value::from(Decimal::ZERO), Value::from(3))
            .unwrap();
        obj.insert(Value::from("".to_string()), Value::from(4))
            .unwrap();

        // Now we ensure it stored as a vector of tuples
        let serialized = serde_json::to_string(&obj).unwrap();
        assert!(serialized.starts_with("[["));

        // Make sure we can deserialize it back
        let obj2 = serde_json::from_str::<ObjectInner>(&serialized).unwrap();
        assert_eq!(obj, obj2);
    }
}
