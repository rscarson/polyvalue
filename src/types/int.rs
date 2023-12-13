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
}
