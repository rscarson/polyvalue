use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

/// Inner type of `Float`
pub type FloatInner = f64;

/// Subtype of `Value` that represents a float
#[derive(PartialOrd, Clone, Serialize, Deserialize, Default, Debug)]
pub struct Float(FloatInner);
impl_value!(Float, FloatInner, |v: &Self| v.inner().to_string());

map_value!(
    from = Float,
    handle_into = |v: Float| Value::Float(v),
    handle_from = |v: Value| match v {
        Value::Float(v) => Ok(v),
        Value::Fixed(v) => {
            let p = *v.inner();
            let p: f64 = p.into();
            Ok(Float::from(p))
        }
        Value::Currency(v) => {
            let p = *v.inner().value().inner();
            let p: f64 = p.into();
            Ok(Float::from(p))
        }
        Value::Int(v) => {
            let p = *v.inner() as f64;
            Ok(Float::from(p))
        }
        Value::Bool(v) => {
            let p = *v.inner() as i64 as f64;
            Ok(Float::from(p))
        }
        Value::String(_) => {
            Err(Error::ValueConversion {
                src_type: ValueType::String,
                dst_type: ValueType::Float,
            })
        }
        Value::Array(v) => {
            if v.inner().len() == 1 {
                let v = v.inner()[0].clone();
                Float::try_from(v)
            } else {
                Err(Error::ValueConversion {
                    src_type: ValueType::Array,
                    dst_type: ValueType::Float,
                })
            }
        }
        Value::Object(v) => {
            if v.inner().len() == 1 {
                let v = v.inner().values().next().unwrap().clone();
                Float::try_from(v)
            } else {
                Err(Error::ValueConversion {
                    src_type: ValueType::Object,
                    dst_type: ValueType::Float,
                })
            }
        }
    }
);

map_type!(Array, Float);
map_type!(Bool, Float);
map_type!(Int, Float);
map_type!(Fixed, Float);
map_type!(Currency, Float);
map_type!(Str, Float);
map_type!(Object, Float);

//
// Trait implementations
//

impl FromStr for Float {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.parse::<FloatInner>()?.into())
    }
}

impl PartialEq for Float {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == std::cmp::Ordering::Equal
    }
}

impl Eq for Float {}

impl Ord for Float {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.inner().is_nan() && other.inner().is_nan() {
            std::cmp::Ordering::Equal
        } else if self.inner().is_nan() {
            std::cmp::Ordering::Less
        } else if other.inner().is_nan() {
            std::cmp::Ordering::Greater
        } else {
            self.inner().partial_cmp(other.inner()).unwrap()
        }
    }
}

impl std::hash::Hash for Float {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner().to_bits().hash(state)
    }
}

impl ArithmeticOperationExt for Float {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = left.inner().clone();
        let right = right.inner().clone();

        let result = match operation {
            ArithmeticOperation::Add => left + right,
            ArithmeticOperation::Subtract => left - right,
            ArithmeticOperation::Multiply => left * right,
            ArithmeticOperation::Divide => left / right,
            ArithmeticOperation::Modulo => left % right,
            ArithmeticOperation::Exponentiate => left.powf(right),
            ArithmeticOperation::Negate => -left,
        };

        if result.is_infinite() || result.is_nan() {
            Err(Error::Overflow)
        } else {
            Ok(result.into())
        }
    }
}
