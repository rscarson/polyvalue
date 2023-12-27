//! Array type
//!
//! The array type is a vector of `Value`s, providing an ordered set
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It will resolve to false when empty, and is represented as a string in
//! the form of `[<value>, <value>, ...]`
//!
use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::hash::Hash;

/// Inner type used for array storage
pub type ArrayInner = Vec<Value>;

/// Subtype of `Value` that represents an array
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Array(ArrayInner);
impl_value!(Array, ArrayInner, |v: &Self| {
    format!(
        "[{}]",
        v.inner()
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<String>>()
            .join(", ")
    )
});

impl Array {
    /// Pop a value from the array
    pub fn pop(&mut self) -> Option<Value> {
        self.inner_mut().pop()
    }

    /// Push a value onto the array
    pub fn push(&mut self, value: Value) {
        self.inner_mut().push(value);
    }

    /// Insert a value into the array
    pub fn insert(&mut self, index: usize, value: Value) {
        self.inner_mut().insert(index, value);
    }

    /// Remove a value from the array
    pub fn remove(&mut self, index: usize) -> Option<Value> {
        if index < self.inner().len() {
            Some(self.inner_mut().remove(index))
        } else {
            None
        }
    }

    /// Get a value from the array, if it exists
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.inner().get(index)
    }

    /// Get a mutable value from the array, if it exists
    pub fn get_mut(&mut self, index: usize) -> Option<&mut Value> {
        self.inner_mut().get_mut(index)
    }

    /// Get the length of the array
    pub fn len(&self) -> usize {
        self.inner().len()
    }

    /// Determine if the array contains any values
    pub fn is_empty(&self) -> bool {
        self.inner().is_empty()
    }
}

map_value!(
    from = Array,
    handle_into = |v: Array| Value::Array(v),
    handle_from = |v: Value| match v {
        Value::Array(v) => Ok(v),
        Value::Int(_) | Value::Bool(_) | Value::Float(_) | Value::Fixed(_) | Value::Currency(_) => {
            Ok(vec![v].into())
        }

        Value::String(s) => {
            let inner = s
                .inner()
                .chars()
                .map(|c| Value::from(c.to_string()))
                .collect::<Vec<_>>();
            Ok(inner.into())
        }

        Value::Object(v) => {
            Ok(v.inner().values().cloned().collect::<ArrayInner>().into())
        }
    }
);

map_type!(Bool, Array);
map_type!(Int, Array);
map_type!(Float, Array);
map_type!(Fixed, Array);
map_type!(Currency, Array);
map_type!(Str, Array);
map_type!(Object, Array);

impl ArithmeticOperationExt for Array {
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
                actual_type: ValueType::Array,
            })?,
        }
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Array::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }
}

impl BooleanOperationExt for Array {
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
            BooleanOperation::Not => right.inner().is_empty(),
        };

        Ok(result.into())
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Array::boolean_op(self, &self.clone(), BooleanOperation::Not)
    }
}

impl IndexingOperationExt for Array {
    fn get_index(&self, index: &Value) -> Result<&Value, crate::Error> {
        let index = *Int::try_from(index.clone())?.inner() as usize;
        self.get(index).ok_or(Error::Index {
            key: index.to_string(),
        })
    }

    fn get_indices(&self, index: &Value) -> Result<Vec<&Value>, crate::Error> {
        let indices = index.as_a::<Array>()?;
        let values = indices
            .inner()
            .iter()
            .map(|i| self.get_index(i))
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(values)
    }

    fn get_index_mut(&mut self, index: &Value) -> Result<&mut Value, crate::Error> {
        let index = *Int::try_from(index.clone())?.inner() as usize;
        self.get_mut(index).ok_or(Error::Index {
            key: index.to_string(),
        })
    }

    fn get_indices_mut(&mut self, index: &Value) -> Result<Vec<&mut Value>, crate::Error> {
        let indices = index
            .as_a::<Array>()?
            .inner()
            .iter()
            .map(|v| Ok(*v.as_a::<Int>()?.inner() as usize))
            .collect::<Result<Vec<_>, Error>>()?;
        self.inner_mut()
            .iter_mut()
            .enumerate()
            .filter(|(i, _)| indices.contains(i))
            .map(|(_, v)| Ok(v))
            .collect::<Result<Vec<_>, Error>>()
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        let index = *Int::try_from(index.clone())?.inner() as usize;
        if index < self.inner().len() {
            self.inner_mut()[index] = value;
            Ok(())
        } else if index == self.inner().len() {
            self.inner_mut().push(value);
            Ok(())
        } else {
            Err(Error::Index {
                key: index.to_string(),
            })?
        }
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
        let mut array = Array::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(array.get_index(&0.into()).unwrap(), &1.into());
        assert_eq!(
            array
                .get_indices(&Array::from(vec![0.into(), 1.into()]).into())
                .unwrap(),
            vec![&1.into(), &2.into()]
        );
        assert_eq!(
            array
                .get_indices(&Array::from(vec![0.into(), 0.into()]).into())
                .unwrap(),
            vec![&1.into(), &1.into()]
        );

        // test get_index_mut
        assert_eq!(array.get_index_mut(&0.into()).unwrap(), &mut 1.into());
        *array.get_index_mut(&0.into()).unwrap() = 4.into();
        assert_eq!(array.get_index_mut(&0.into()).unwrap(), &mut 4.into());

        // test set_index
        array.set_index(&0.into(), 5.into()).unwrap();
        assert_eq!(array.get_index(&0.into()).unwrap(), &5.into());
    }

    #[test]
    fn test_arithmetic() {
        let array = Array::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(
            Array::arithmetic_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into()]),
                ArithmeticOperation::Add
            )
            .unwrap(),
            Array::from(vec![
                1.into(),
                2.into(),
                3.into(),
                1.into(),
                2.into(),
                3.into()
            ])
        );
    }

    #[test]
    fn test_boolean_logic() {
        let array = Array::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(
            Array::boolean_op(&array, &Array::from(vec![]), BooleanOperation::And).unwrap(),
            false.into()
        );
        assert_eq!(
            Array::boolean_op(&array, &Array::from(vec![]), BooleanOperation::Or).unwrap(),
            true.into()
        );
        assert_eq!(
            Array::boolean_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into()]),
                BooleanOperation::LT
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Array::boolean_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into()]),
                BooleanOperation::GT
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Array::boolean_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into()]),
                BooleanOperation::LTE
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Array::boolean_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into()]),
                BooleanOperation::GTE
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Array::boolean_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into()]),
                BooleanOperation::EQ
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Array::boolean_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into()]),
                BooleanOperation::NEQ
            )
            .unwrap(),
            false.into()
        );
    }

    #[test]
    fn test_to_string() {
        let array = Array::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(array.to_string(), "[1, 2, 3]");
    }

    #[test]
    fn test_from() {
        let array = Array::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(array, vec![1.into(), 2.into(), 3.into()].into());

        let array = Array::try_from(Value::from(1)).unwrap();
        assert_eq!(array, vec![1.into()].into());

        let array = Array::try_from(Value::from(1.0)).unwrap();
        assert_eq!(array, vec![1.0.into()].into());

        let array = Array::try_from(Value::from(Dec!(1.0))).unwrap();
        assert_eq!(array, vec![Dec!(1.0).into()].into());

        let currency = Currency::from_fixed(Dec!(1.0).into());
        let array = Array::try_from(Value::from(currency.clone())).unwrap();
        assert_eq!(array, vec![currency.into()].into());

        let array = Array::try_from(Value::from("hello")).unwrap();
        assert_eq!(array, vec!["hello".into()].into());

        let array = Array::try_from(Value::from(true)).unwrap();
        assert_eq!(array, vec![true.into()].into());

        let object = Object::from(vec![("a".into(), 1.into())]);
        let array = Array::try_from(Value::from(object.clone())).unwrap();
        assert_eq!(array, vec![1.into()].into());
    }
}
