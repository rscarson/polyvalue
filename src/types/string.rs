use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};

/// Subtype of `Value` that represents a string
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug)]
pub struct Str(String);
impl_value!(Str, String, |v: &Self| v.inner().clone());

impl From<&str> for Str {
    fn from(value: &str) -> Self {
        <Str>::new(value.to_string())
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        <Str>::new(value.to_string()).into()
    }
}

map_value!(
    from = Str,
    handle_into = |v: Str| Value::String(v),
    handle_from = |v: Value| match v {
        Value::String(v) => Ok(v),
        _ => Ok(Str::from(v.to_string())),
    }
);

map_type!(Bool, Str);
map_type!(Int, Str);
map_type!(Float, Str);
map_type!(Fixed, Str);
map_type!(Currency, Str);
map_type!(Array, Str);
map_type!(Object, Str);

impl ArithmeticOperationExt for Str {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = left.inner().to_string();
        let right = right.inner().to_string();
        let result = match operation {
            ArithmeticOperation::Add => left + right.as_str(),
            ArithmeticOperation::Subtract => left.replace(&right, ""),
            _ => Err(Error::UnsupportedOperation {
                operation: operation,
                actual_type: ValueType::String,
            })?,
        };
        Ok(result.into())
    }
}
