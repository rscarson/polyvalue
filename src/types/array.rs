//! Array type
//!
//! The array type is a vector of `Value`s, providing an ordered set
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It will resolve to false when empty, and is represented as a string in
//! the form of `[<value>, <value>, ...]`
//!
use crate::{operations::*, types::*, Error, InnerValue, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::hash::Hash;

/// Inner type used for array storage
pub type ArrayInner = Vec<Value>;
pub type ArrayIndex = <I64 as ValueTrait>::Inner;

/// Subtype of `Value` that represents an array
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Array(ArrayInner);
impl_value!(
    Array,
    ArrayInner,
    |v: &Self| {
        format!(
            "[{}]",
            v.inner()
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        )
    },
    |v: &Self, f: &mut std::fmt::Formatter<'_>| {
        write!(
            f,
            "[{}]",
            v.inner()
                .iter()
                .map(|v| format!("{:?}", v))
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
);

impl Array {
    /// Largest range that can be converted to an array
    pub const MAX_CONVERTIBLE_RANGE: usize = 0x10000;

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

    /// Preallocate space for a large array conversion
    pub fn prealloc_range_conversion(length: usize) -> Result<Self, Error> {
        if length > Self::MAX_CONVERTIBLE_RANGE {
            return Err(Error::RangeTooLarge { length })?;
        }

        let mut container = ArrayInner::new();
        if let Err(e) = container.try_reserve(length) {
            return Err(Error::from(e));
        }

        Ok(container.into())
    }
}

map_value!(
    from = Array,
    handle_into = Value::array,
    handle_from = |v: Value| match v.inner() {
        InnerValue::Array(v) => Ok(v.clone()),
        InnerValue::Range(v) => {
            let length = (v.inner().end() - v.inner().start()) as usize;
            let mut container = Array::prealloc_range_conversion(length)?;
            for i in v.inner().clone() {
                container.push(Value::from(i));
            }
            Ok(container)
        }

        InnerValue::Bool(_)
        | InnerValue::Float(_)
        | InnerValue::Fixed(_)
        | InnerValue::Currency(_)
        | InnerValue::U8(_)
        | InnerValue::U16(_)
        | InnerValue::U32(_)
        | InnerValue::U64(_)
        | InnerValue::I8(_)
        | InnerValue::I16(_)
        | InnerValue::I32(_)
        | InnerValue::I64(_) => {
            Ok(vec![v].into())
        }

        InnerValue::String(s) => {
            let inner = s
                .inner()
                .chars()
                .map(|c| Value::from(c.to_string()))
                .collect::<Vec<_>>();
            Ok(inner.into())
        }

        InnerValue::Object(v) => {
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
map_type!(Range, Array);

overload_operator!(Array, add);
overload_operator!(Array, sub);
overload_operator!(Array, neg);
overload_operator!(Array, deref);

impl MatchingOperationExt for Array {
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
                let pattern = pattern.clone().as_a::<Array>()?;
                container
                    .inner()
                    .iter()
                    .any(|v| pattern.inner().contains(v))
            }
            MatchingOperation::StartsWith => {
                let pattern = pattern.clone().as_a::<Array>()?;
                container.inner().starts_with(pattern.inner())
            }
            MatchingOperation::EndsWith => {
                let pattern = pattern.clone().as_a::<Array>()?;
                container.inner().ends_with(pattern.inner())
            }
            MatchingOperation::Matches => {
                let pattern = pattern.clone().as_a::<Array>()?;
                container.inner().iter().eq(pattern.inner().iter())
            }

            // Handled by Value
            _ => false,
        };

        Ok(result.into())
    }
}

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

            ArithmeticOperation::Subtract => {
                let mut result = left.clone();
                let rset = std::collections::HashSet::<&Value>::from_iter(right.inner().iter());
                result.inner_mut().retain(|v| !rset.contains(v));
                Ok(result)
            }

            // reverse
            ArithmeticOperation::Negate => {
                let mut result = left.clone();
                result.inner_mut().reverse();
                Ok(result)
            }

            _ => Err(Error::UnsupportedOperation {
                operation: operation.to_string(),
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

    fn is_operator_supported(&self, _other: &Self, operation: ArithmeticOperation) -> bool {
        matches!(
            operation,
            ArithmeticOperation::Add | ArithmeticOperation::Subtract | ArithmeticOperation::Negate
        )
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
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        let mut index = *I64::try_from(index.clone())?.inner();
        if index < 0 {
            index += self.inner().len() as ArrayIndex;
        }
        let index = index as usize;

        let result = self.get(index).ok_or(Error::Index {
            key: index.to_string(),
        })?;

        Ok(result.clone())
    }

    fn get_indices(&self, index: &Value) -> Result<Value, crate::Error> {
        if index.is_a(ValueType::Range) {
            let indices = index.clone().as_a::<Range>()?;
            let values = indices
                .inner()
                .clone()
                .map(|i| self.get_index(&Value::from(i)))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::from(values))
        } else {
            let indices = index.clone().as_a::<Array>()?;
            let values = indices
                .inner()
                .iter()
                .map(|i| self.get_index(i))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::from(values))
        }
    }
}

impl IndexingMutationExt for Array {
    fn get_index_mut(&mut self, index: &Value) -> Result<&mut Value, crate::Error> {
        let mut index = *I64::try_from(index.clone())?.inner();
        if index < 0 {
            index += self.inner().len() as ArrayIndex
        }
        let index = index as usize;

        self.get_mut(index).ok_or(Error::Index {
            key: index.to_string(),
        })
    }

    fn get_indices_mut(&mut self, index: &Value) -> Result<Vec<&mut Value>, crate::Error> {
        let indices = index
            .clone()
            .as_a::<Array>()?
            .inner()
            .iter()
            .map(|v| Ok(*v.clone().as_a::<I64>()?.inner() as usize))
            .collect::<Result<Vec<_>, Error>>()?;
        self.inner_mut()
            .iter_mut()
            .enumerate()
            .filter(|(i, _)| indices.contains(i))
            .map(|(_, v)| Ok(v))
            .collect::<Result<Vec<_>, Error>>()
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        let mut index = *I64::try_from(index.clone())?.inner();
        if index < 0 {
            index += self.inner().len() as ArrayIndex
        }
        let index = index as usize;

        match index.cmp(&self.inner().len()) {
            std::cmp::Ordering::Less => self.inner_mut()[index] = value,
            std::cmp::Ordering::Equal => self.inner_mut().push(value),

            std::cmp::Ordering::Greater => {
                return Err(Error::Index {
                    key: index.to_string(),
                })?
            }
        }
        Ok(())
    }

    fn insert_at(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        let mut index = *I64::try_from(index.clone())?.inner();
        if index < 0 {
            index += self.inner().len() as ArrayIndex
        }
        let index = index as usize;

        if index <= self.inner().len() {
            self.inner_mut().insert(index, value);
            Ok(())
        } else {
            Err(Error::Index {
                key: index.to_string(),
            })?
        }
    }

    fn delete_index(&mut self, index: &Value) -> Result<Value, crate::Error> {
        let mut index = *I64::try_from(index.clone())?.inner();
        if index < 0 {
            index += self.inner().len() as ArrayIndex
        }
        let index = index as usize;

        if index < self.inner().len() {
            Ok(self.inner_mut().remove(index))
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
    use super::*;
    use crate::fixed;
    use fpdec::Decimal;

    #[test]
    fn test_innerarray_impl() {
        let mut array = Array::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(array.pop().unwrap(), 3.into());
        array.push(4.into());
        assert_eq!(array.pop().unwrap(), 4.into());
        array.insert(0, 5.into());
        assert_eq!(array.pop().unwrap(), 2.into());
        assert_eq!(array.pop().unwrap(), 1.into());
        assert_eq!(array.pop().unwrap(), 5.into());
        assert_eq!(array.pop(), None);
        array.push(1.into());
        array.push(2.into());
        array.push(3.into());
        assert_eq!(array.remove(1).unwrap(), 2.into());
        assert_eq!(array.remove(1).unwrap(), 3.into());
        assert_eq!(array.remove(0).unwrap(), 1.into());
        assert_eq!(array.remove(0), None);
        assert_eq!(array.len(), 0);
        assert!(array.is_empty());

        let mut array = Array::from(vec![1.into(), 2.into(), 3.into()]);
        array.insert(1, 4.into());
        assert_eq!(array.pop().unwrap(), 3.into());
    }

    #[test]
    fn test_matching() {
        let array = Array::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(
            Array::matching_op(&array, &1.into(), MatchingOperation::Contains).unwrap(),
            true.into()
        );
        assert_eq!(
            Array::matching_op(&array, &4.into(), MatchingOperation::Contains).unwrap(),
            false.into()
        );
        assert_eq!(
            Array::matching_op(
                &array,
                &Array::from(vec![1.into()]).into(),
                MatchingOperation::Contains
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Array::matching_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into()]).into(),
                MatchingOperation::Matches
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Array::matching_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into(), 4.into()]).into(),
                MatchingOperation::Matches
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Array::matching_op(
                &array,
                &Array::from(vec![1.into(), 2.into(), 3.into()]).into(),
                MatchingOperation::StartsWith
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Array::matching_op(
                &array,
                &Array::from(vec![1.into(), 2.into()]).into(),
                MatchingOperation::StartsWith
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Array::matching_op(
                &array,
                &Array::from(vec![1.into()]).into(),
                MatchingOperation::StartsWith
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Array::matching_op(
                &array,
                &Array::from(vec![2.into(), 3.into()]).into(),
                MatchingOperation::StartsWith
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Array::matching_op(
                &array,
                &Array::from(vec![2.into(), 3.into()]).into(),
                MatchingOperation::EndsWith
            )
            .unwrap(),
            true.into()
        );
    }

    #[test]
    fn test_indexing() {
        let mut array = Array::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(array.get_index(&0.into()).unwrap(), 1.into());
        assert_eq!(array.get_index(&(-1).into()).unwrap(), 3.into());
        assert_eq!(
            array
                .get_indices(&Array::from(vec![0.into(), 1.into()]).into())
                .unwrap(),
            Value::from(vec![1.into(), 2.into()])
        );
        assert_eq!(
            array
                .get_indices(&Array::from(vec![0.into(), 0.into()]).into())
                .unwrap(),
            Value::from(vec![1.into(), 1.into()])
        );

        // test get_index_mut
        assert_eq!(array.get_index_mut(&0.into()).unwrap(), &mut 1.into());
        *array.get_index_mut(&0.into()).unwrap() = 4.into();
        assert_eq!(array.get_index_mut(&0.into()).unwrap(), &mut 4.into());

        array.delete_index(&99.into()).unwrap_err();

        // test set_index
        array.set_index(&99.into(), 5.into()).unwrap_err();
        array.set_index(&0.into(), 5.into()).unwrap();
        assert_eq!(array.get_index(&0.into()).unwrap(), 5.into());

        // test negative index
        assert_eq!(array.get_index(&(-1).into()).unwrap(), 3.into());
        array.set_index(&(-1).into(), 6.into()).unwrap();
        assert_eq!(array.get_index(&(-1).into()).unwrap(), 6.into());

        // test index==len
        array.set_index(&3.into(), 7.into()).unwrap();
        assert_eq!(array.get_index(&(-1).into()).unwrap(), 7.into());
        array.delete_index(&(-1).into()).unwrap();

        // get by range
        assert_eq!(
            array.get_indices(&Value::from(0..=1)).unwrap(),
            Value::from(vec![5.into(), 2.into()])
        );

        // get_index_mut when index<0
        assert_eq!(array.get_index_mut(&(-1).into()).unwrap(), &mut 6.into());
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

        assert_eq!(
            Array::arithmetic_op(
                &array,
                &Array::from(vec![1.into(), 2.into()]),
                ArithmeticOperation::Subtract
            )
            .unwrap(),
            Array::from(vec![3.into()])
        );

        assert_eq!(
            Array::arithmetic_neg(&array).unwrap(),
            Array::from(vec![3.into(), 2.into(), 1.into()])
        );

        assert!(Array::is_operator_supported(
            &array,
            &array,
            ArithmeticOperation::Add
        ));

        assert!(!Array::is_operator_supported(
            &array,
            &array,
            ArithmeticOperation::Exponentiate
        ));
        assert!(Array::arithmetic_op(&array, &array, ArithmeticOperation::Exponentiate).is_err())
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
        assert_eq!(
            Array::boolean_op(&array, &Array::from(vec![]), BooleanOperation::Not).unwrap(),
            true.into()
        );
        assert_eq!(
            Array::boolean_op(&array, &Array::from(vec![1.into()]), BooleanOperation::Not).unwrap(),
            false.into()
        );

        assert_eq!(Array::boolean_not(&array).unwrap(), false.into());
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

        let array = Array::try_from(Value::from(fixed!(1.0))).unwrap();
        assert_eq!(array, vec![fixed!(1.0).into()].into());

        let currency = Currency::from_fixed(fixed!(1.0));
        let array = Array::try_from(Value::from(currency.clone())).unwrap();
        assert_eq!(array, vec![currency.into()].into());

        let array = Array::try_from(Value::from("hello")).unwrap();
        assert_eq!(array.len(), 5);

        let array = Array::try_from(Value::from(true)).unwrap();
        assert_eq!(array, vec![true.into()].into());

        let object = Object::try_from(vec![("a".into(), 1.into())]).unwrap();
        let array = Array::try_from(Value::from(object.clone())).unwrap();
        assert_eq!(array, vec![1.into()].into());

        let range = Range::new(1..=2);
        let array = Array::try_from(Value::from(range.clone())).unwrap();
        assert_eq!(array, vec![Value::i64(1), Value::i64(2)].into());

        let range = Range::new(0..=0);
        let array = Array::try_from(Value::from(range.clone())).unwrap();
        assert_eq!(array, vec![Value::i64(0)].into());
    }

    #[test]
    fn test_giant_range() {
        let range = Range::new(0..=0xf7767700);
        let _ = Array::try_from(Value::from(range.clone()));
    }
}
