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

pub use crate::inner_object::ObjectInner;

/// Subtype of `Value` that represents an object
#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Default, Debug, Hash, PartialOrd, Ord)]
pub struct Object(ObjectInner);
impl_value!(Object, ObjectInner, |v: &Self| {
    let mut v = v.inner().iter().collect::<Vec<_>>();
    v.sort_by_key(|(k, _)| *k);
    format!(
        "{{{}}}",
        v.iter()
            .map(|(k, v)| format!("{k}: {v}"))
            .collect::<Vec<String>>()
            .join(", ")
    )
});

impl TryFrom<Vec<(Value, Value)>> for Value {
    type Error = Error;
    fn try_from(value: Vec<(Value, Value)>) -> Result<Self, Self::Error> {
        Ok(Object::try_from(value)?.into())
    }
}

impl TryFrom<Vec<(Value, Value)>> for Object {
    type Error = Error;
    fn try_from(value: Vec<(Value, Value)>) -> Result<Self, Self::Error> {
        Ok(ObjectInner::try_from(value)?.into())
    }
}

impl Object {
    /// Insert a key-value pair into the object
    /// If the key already exists, it will be overwritten
    pub fn insert(&mut self, key: Value, value: Value) -> Result<Option<Value>, Error> {
        self.inner_mut().insert(key, value)
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
    handle_into = Value::Object,
    handle_from = |v: Value| match v {
        Value::Range(_) => Self::try_from(v.as_a::<Array>()?),
        Value::Object(v) => Ok(v),

        Value::Int(_)
        | Value::String(_)
        | Value::Bool(_)
        | Value::Float(_)
        | Value::Fixed(_)
        | Value::Currency(_)
        | Value::U8(_)
        | Value::U16(_)
        | Value::U32(_)
        | Value::U64(_)
        | Value::I8(_)
        | Value::I16(_)
        | Value::I32(_)
        | Value::I64(_) => {
            let mut map = ObjectInner::new();
            map.insert(Value::Int(Int::from(0)), v).ok();
            Ok(Object(map))
        }

        Value::Array(v) => {
            let mut map = ObjectInner::new();
            for (i, v) in v.inner().iter().enumerate() {
                map.insert(Value::Int((i as i64).into()), v.clone()).ok();
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
map_type!(Range, Object);

overload_operator!(Object, add);
overload_operator!(Object, deref);

//
// Trait implementations
//

impl MatchingOperationExt for Object {
    fn matching_op(
        container: &Self,
        pattern: &Value,
        operation: MatchingOperation,
    ) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        let result = match operation {
            MatchingOperation::Contains => {
                let pattern = pattern.as_a::<Array>()?;
                pattern
                    .inner()
                    .iter()
                    .all(|p| container.inner().contains_key(p))
            }
            MatchingOperation::StartsWith | MatchingOperation::EndsWith => {
                return Err(Error::UnsupportedOperation {
                    operation: operation.to_string(),
                    actual_type: ValueType::Object,
                })?
            }
            MatchingOperation::Matches => {
                let pattern = pattern.as_a::<Object>()?;
                container.inner().eq(pattern.inner())
            }

            // Handled by Value
            _ => false,
        };

        Ok(result.into())
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
                operation: operation.to_string(),
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

    fn is_operator_supported(&self, _: &Self, operation: ArithmeticOperation) -> bool {
        match operation {
            ArithmeticOperation::Add => true,
            _ => false,
        }
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
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        let result = self.get(index).ok_or(Error::Index {
            key: index.to_string(),
        })?;
        Ok(result.clone())
    }

    fn get_indices(&self, index: &Value) -> Result<Value, Error> {
        if index.is_a(ValueType::Range) {
            let indices = index.as_a::<Range>()?;
            let values = indices
                .inner()
                .clone()
                .map(|i| self.get_index(&Value::from(i)))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::from(values))
        } else {
            let indices = index.as_a::<Array>()?;
            let values = indices
                .inner()
                .iter()
                .map(|i| self.get_index(i))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::from(values))
        }
    }
}

impl IndexingMutationExt for Object {
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
        self.inner_mut().insert(index.clone(), value)?;
        Ok(())
    }

    fn delete_index(&mut self, index: &Value) -> Result<Value, crate::Error> {
        self.inner_mut().remove(index).ok_or(Error::Index {
            key: index.to_string(),
        })
    }
}

//
// Tests
//

#[cfg(test)]
mod test {
    use fpdec::{Dec, Decimal};

    use super::*;

    #[test]
    fn test_indexing() {
        let mut obj = Object::try_from(vec![
            (Value::Int(0.into()), Value::Int(1.into())),
            (Value::Int(1.into()), Value::Int(2.into())),
            (Value::Int(2.into()), Value::Int(3.into())),
        ])
        .unwrap();

        assert_eq!(obj.get(&Value::Int(0.into())), Some(&Value::Int(1.into())));
        assert_eq!(obj.get(&Value::Int(1.into())), Some(&Value::Int(2.into())));
        assert_eq!(obj.get(&Value::Int(2.into())), Some(&Value::Int(3.into())));
        assert_eq!(obj.get(&Value::Int(3.into())), None);

        let indices = obj
            .get_indices(&Value::Array(Array::from(vec![
                Value::Int(0.into()),
                Value::Int(2.into()),
            ])))
            .unwrap()
            .as_a::<Array>()
            .unwrap()
            .inner()
            .clone();
        assert!(indices.contains(&Value::Int(1.into())));
        assert!(indices.contains(&Value::Int(3.into())));

        obj.set_index(&Value::Int(3.into()), Value::Int(4.into()))
            .unwrap();
        assert_eq!(obj.get(&Value::Int(3.into())), Some(&Value::Int(4.into())));

        let indices = obj
            .get_indices(&Value::Range(Range::from(0..=2)))
            .unwrap()
            .as_a::<Array>()
            .unwrap()
            .inner()
            .clone();
        assert!(indices.contains(&Value::Int(1.into())));
        assert!(indices.contains(&Value::Int(2.into())));
        assert!(indices.contains(&Value::Int(3.into())));

        // delete index
        assert_eq!(
            obj.delete_index(&Value::Int(3.into())).unwrap(),
            Value::Int(4.into())
        );
        assert_eq!(obj.get(&Value::Int(3.into())), None);
    }

    #[test]
    fn test_arithmetic() {
        let result = Object::arithmetic_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            ArithmeticOperation::Add,
        )
        .unwrap();
        assert_eq!(
            result,
            Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap()
        );

        assert!(Object::arithmetic_neg(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap()
        )
        .is_err());

        assert_eq!(
            Object::is_operator_supported(
                &Object::try_from(vec![
                    (Value::Int(0.into()), Value::Int(1.into())),
                    (Value::Int(1.into()), Value::Int(2.into())),
                ])
                .unwrap(),
                &Object::try_from(vec![
                    (Value::Int(0.into()), Value::Int(3.into())),
                    (Value::Int(1.into()), Value::Int(4.into())),
                ])
                .unwrap(),
                ArithmeticOperation::Add
            ),
            true
        );

        assert_eq!(
            Object::is_operator_supported(
                &Object::try_from(vec![
                    (Value::Int(0.into()), Value::Int(1.into())),
                    (Value::Int(1.into()), Value::Int(2.into())),
                ])
                .unwrap(),
                &Object::try_from(vec![
                    (Value::Int(0.into()), Value::Int(3.into())),
                    (Value::Int(1.into()), Value::Int(4.into())),
                ])
                .unwrap(),
                ArithmeticOperation::Subtract
            ),
            false
        );

        let result = Object::arithmetic_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            ArithmeticOperation::Subtract,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_boolean_logic() {
        let result = Object::boolean_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            BooleanOperation::And,
        )
        .unwrap();
        assert_eq!(result, Value::from(true));

        let result = Object::boolean_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            BooleanOperation::Or,
        )
        .unwrap();
        assert_eq!(result, Value::from(true));

        let result = Object::boolean_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            BooleanOperation::LT,
        )
        .unwrap();
        assert_eq!(result, Value::from(true));

        let result = Object::boolean_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
                (Value::Int(2.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            BooleanOperation::GT,
        )
        .unwrap();
        assert_eq!(result, Value::from(false));

        let result = Object::boolean_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            BooleanOperation::LTE,
        )
        .unwrap();
        assert_eq!(result, Value::from(true));

        let result = Object::boolean_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            BooleanOperation::GTE,
        )
        .unwrap();
        assert_eq!(result, Value::from(false));

        let result = Object::boolean_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            BooleanOperation::EQ,
        )
        .unwrap();
        assert_eq!(result, Value::from(false));

        let result = Object::boolean_op(
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap(),
            &Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(3.into())),
                (Value::Int(1.into()), Value::Int(4.into())),
            ])
            .unwrap(),
            BooleanOperation::NEQ,
        )
        .unwrap();
        assert_eq!(result, Value::from(true));

        let result = Object::boolean_op(
            &Object::try_from(vec![]).unwrap(),
            &Object::try_from(vec![]).unwrap(),
            BooleanOperation::Not,
        )
        .unwrap();
        assert_eq!(result, Value::from(true));

        assert_eq!(
            Object::boolean_not(&Object::try_from(vec![]).unwrap()).unwrap(),
            Value::from(true)
        );
    }

    #[test]
    fn test_to_string() {
        assert_eq!(
            Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap()
            .to_string(),
            "{0: 1, 1: 2}"
        );
    }

    #[test]
    fn test_from() {
        assert_eq!(
            Object::try_from(
                Value::try_from(vec![
                    (Value::Int(0.into()), Value::Int(1.into())),
                    (Value::Int(1.into()), Value::Int(2.into())),
                ])
                .unwrap()
            )
            .unwrap(),
            Object::try_from(vec![
                (Value::Int(0.into()), Value::Int(1.into())),
                (Value::Int(1.into()), Value::Int(2.into())),
            ])
            .unwrap()
        );

        assert_eq!(
            Object::try_from(
                Value::try_from(vec![(Value::Int(0.into()), Value::Int(1.into()))]).unwrap()
            )
            .unwrap(),
            Object::try_from(vec![(Value::Int(0.into()), Value::Int(1.into()))]).unwrap()
        );

        assert_eq!(
            Object::try_from(Value::from(1)).unwrap(),
            Object::try_from(vec![(Value::Int(0.into()), Value::Int(1.into()))]).unwrap()
        );

        assert_eq!(
            Object::try_from(Value::from(1.0)).unwrap(),
            Object::try_from(vec![(Value::Int(0.into()), Value::Float(1.0.into()))]).unwrap()
        );

        assert_eq!(
            Object::try_from(Value::from(Dec!(1.0))).unwrap(),
            Object::try_from(vec![(Value::Int(0.into()), Value::from(Dec!(1.0)))]).unwrap()
        );

        assert_eq!(
            Object::try_from(Value::from("true")).unwrap(),
            Object::try_from(vec![(Value::Int(0.into()), Value::from("true"))]).unwrap()
        );

        assert_eq!(
            Object::try_from(Value::from(true)).unwrap(),
            Object::try_from(vec![(Value::Int(0.into()), Value::Bool(true.into()))]).unwrap()
        );

        let value = Value::from(0..=99999999);
        assert!(Object::try_from(value).is_err());
    }

    #[test]
    fn test_obj_impl() {
        let mut obj = Object::try_from(vec![
            (Value::Int(0.into()), Value::Int(1.into())),
            (Value::Int(1.into()), Value::Int(2.into())),
        ])
        .unwrap();

        assert_eq!(obj.get(&Value::Int(0.into())), Some(&Value::Int(1.into())));
        assert_eq!(obj.get(&Value::Int(1.into())), Some(&Value::Int(2.into())));
        assert_eq!(obj.get(&Value::Int(2.into())), None);

        assert_eq!(obj.is_empty(), false);

        assert!(obj.keys().contains(&&Value::Int(0.into())));

        assert_eq!(obj.values().len(), 2);

        assert_eq!(
            obj.insert(Value::Int(2.into()), Value::Int(3.into()))
                .unwrap(),
            None
        );
        assert_eq!(obj.get(&Value::Int(2.into())), Some(&Value::Int(3.into())));

        assert_eq!(
            obj.insert(Value::Int(2.into()), Value::Int(4.into()))
                .unwrap(),
            Some(Value::Int(3.into()))
        );
        assert_eq!(obj.get(&Value::Int(2.into())), Some(&Value::Int(4.into())));

        assert_eq!(
            obj.remove(&Value::Int(2.into())),
            Some(Value::Int(4.into()))
        );
        assert_eq!(obj.get(&Value::Int(2.into())), None);

        assert_eq!(obj.remove(&Value::Int(2.into())), None);
    }
}
