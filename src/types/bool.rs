use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use fpdec::Decimal;
use serde::{Deserialize, Serialize};
use std::{hash::Hash, str::FromStr};

/// Subtype of `Value` that represents a boolean
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Bool(bool);
impl_value!(Bool, bool, |v: &Self| if *v.inner() {
    "true"
} else {
    "false"
});

map_value!(
    from = Bool,
    handle_into = |v: Bool| Value::Bool(v),
    handle_from = |v: Value| match v {
        Value::Bool(v) => Ok(v),
        Value::Int(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }
        Value::Float(v) => {
            Ok(Bool::from(*v.inner() != 0.0))
        }
        Value::Fixed(v) => {
            Ok(Bool::from(*v.inner() != Decimal::ZERO))
        }
        Value::Currency(v) => {
            Ok(Bool::from(*v.inner().value().inner() == Decimal::ZERO).into())
        }
        Value::String(v) => {
            Ok(Bool::from(!v.inner().is_empty()))
        }
        Value::Array(v) => {
            Ok(Bool::from(!v.inner().is_empty()))
        }
        Value::Object(v) => {
            Ok(Bool::from(!v.inner().is_empty()))
        }
    }
);

impl FromStr for Bool {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "true" => Ok(Bool::from(true)),
            "false" => Ok(Bool::from(false)),
            _ => Err(Error::ValueConversion {
                src_type: ValueType::String,
                dst_type: ValueType::Bool,
            }),
        }
    }
}

map_type!(Array, Bool);
map_type!(Object, Bool);
map_type!(Int, Bool);
map_type!(Float, Bool);
map_type!(Fixed, Bool);
map_type!(Currency, Bool);
map_type!(Str, Bool);

impl ArithmeticOperationExt for Bool {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = Int::try_from(Value::from(left.clone()))?;
        let right = Int::try_from(Value::from(right.clone()))?;
        let result = Int::arithmetic_op(&left, &right, operation)?;
        Ok(Value::from(result).try_into()?)
    }
}
