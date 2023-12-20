//! Int type
//!
//! This type represents an integer. It is a wrapper around `i64`
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use std::str::FromStr;

use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};

/// Inner type of `Int`
pub type IntInner = i64;

/// Subtype of `Value` that represents an integer
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug)]
pub struct Int(IntInner);
impl_value!(Int, IntInner, |v: &Self| v.inner().to_string());

map_value!(
    from = Int,
    handle_into = |v: Int| Value::Int(v),
    handle_from = |v: Value| match v {
        Value::Int(v) => Ok(v),
        Value::Fixed(v) => {
            let p = *v.inner();
            let p: IntInner = p.trunc().coefficient() as IntInner;
            Ok(Int::from(p))
        }
        Value::Float(v) => {
            let p = *v.inner();
            let p = p as i64;
            Ok(Int::from(p))
        }
        Value::Currency(v) => {
            let p = *v.inner().value().inner();
            let p: IntInner = p.trunc().coefficient() as IntInner;
            Ok(Int::from(p))
        }
        Value::Bool(v) => {
            let p = *v.inner() as i64;
            Ok(Int::from(p))
        }
        Value::String(_) => {
            Err(Error::ValueConversion {
                src_type: ValueType::String,
                dst_type: ValueType::Int,
            })
        }
        Value::Array(v) => {
            if v.inner().len() == 1 {
                let v = v.inner()[0].clone();
                Int::try_from(v)
            } else {
                Err(Error::ValueConversion {
                    src_type: ValueType::Array,
                    dst_type: ValueType::Int,
                })
            }
        }
        Value::Object(v) => {
            if v.inner().len() == 1 {
                let v = v.inner().values().next().unwrap().clone();
                Int::try_from(v)
            } else {
                Err(Error::ValueConversion {
                    src_type: ValueType::Object,
                    dst_type: ValueType::Int,
                })
            }
        }
    }
);

impl From<usize> for Value {
    fn from(v: usize) -> Self {
        Int::from(v).into()
    }
}

impl From<usize> for Int {
    fn from(v: usize) -> Self {
        Int(v as IntInner)
    }
}

impl From<i32> for Value {
    fn from(v: i32) -> Self {
        Int::from(v).into()
    }
}

impl From<i32> for Int {
    fn from(v: i32) -> Self {
        Int(v as IntInner)
    }
}

impl FromStr for Int {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.parse::<IntInner>()?.into())
    }
}

map_type!(Array, Int);
map_type!(Bool, Int);
map_type!(Fixed, Int);
map_type!(Float, Int);
map_type!(Currency, Int);
map_type!(Str, Int);
map_type!(Object, Int);

impl ArithmeticOperationExt for Int {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = left.inner().clone();
        let right = right.inner().clone();

        let result = match operation {
            ArithmeticOperation::Add => left.checked_add(right),
            ArithmeticOperation::Subtract => left.checked_sub(right),
            ArithmeticOperation::Multiply => left.checked_mul(right),
            ArithmeticOperation::Divide => left.checked_div(right),
            ArithmeticOperation::Modulo => left.checked_rem(right),
            ArithmeticOperation::Exponentiate => {
                if let Ok(right) = right.try_into() {
                    left.checked_pow(right)
                } else {
                    None
                }
            }
            ArithmeticOperation::Negate => Some(-left),
        }
        .ok_or(Error::Overflow)?;
        Ok(result.into())
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Int::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }
}

impl BooleanOperationExt for Int {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => *left.inner() == 0 && *right.inner() == 0,
            BooleanOperation::Or => *left.inner() == 0 || *right.inner() == 0,

            BooleanOperation::LT => *left.inner() < *right.inner(),
            BooleanOperation::GT => *left.inner() > *right.inner(),
            BooleanOperation::LTE => *left.inner() <= *right.inner(),
            BooleanOperation::GTE => *left.inner() >= *right.inner(),
            BooleanOperation::EQ => *left.inner() == *right.inner(),
            BooleanOperation::NEQ => *left.inner() != *right.inner(),
            BooleanOperation::Not => *left.inner() != 0,
        };

        Ok(result.into())
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Int::boolean_op(self, &self.clone(), BooleanOperation::Not)
    }
}
