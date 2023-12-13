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

map_value!(
    from = Array,
    handle_into = |v: Array| Value::Array(v),
    handle_from = |v: Value| match v {
        Value::Array(v) => Ok(v),
        Value::Int(_)
        | Value::Bool(_)
        | Value::Float(_)
        | Value::Fixed(_)
        | Value::Currency(_)
        | Value::String(_) => {
            Ok(vec![v].into())
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
}

impl IndexingOperationExt for Array {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        let index = *Int::try_from(index.clone())?.inner() as usize;
        if let Some(value) = self.inner().get(index) {
            Ok(value.clone())
        } else {
            Err(Error::Index {
                key: index.to_string(),
            })?
        }
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        let index = *Int::try_from(index.clone())?.inner() as usize;
        if index > 0 && index <= self.inner().len() {
            self.inner_mut().insert(index, value);
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
