use crate::{operations::*, types::*, Error, Value, ValueTrait};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

/// Inner type of `Float`
pub type FloatInner = f64;

/// Subtype of `Value` that represents a float
#[derive(PartialEq, PartialOrd, Clone, Serialize, Deserialize, Default)]
pub struct Float(FloatInner);
impl_value!(Float, FloatInner);

map_value!(
    from = Float,
    handle_into = |v: Float| Value::Float(v),
    handle_from = |v: Value| match v {
        Value::Float(v) => Ok(v),
        Value::Fixed(v) => v.try_into(),
        Value::Currency(v) => v.try_into(),
        Value::Int(v) => v.try_into(),
        Value::Bool(v) => v.try_into(),
        Value::String(v) => v.try_into(),
        Value::Array(v) => v.try_into(),
        Value::Object(v) => v.try_into(),
    }
);

//
// Trait implementations
//

impl FromStr for Float {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.parse::<FloatInner>()?.into())
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

//
// Conversion from other types
//

map_type!(into = Bool, from = Float, |v: Float| {
    Ok((*v.inner() != 0.0).into())
});

map_type!(into = Fixed, from = Float, |v: Float| {
    Fixed::from_str(&v.to_string())
});

map_type!(into = Currency, from = Float, |v: Float| {
    Ok(Currency::without_symbol(v.try_into().unwrap()).into())
});

map_type!(into = Int, from = Float, |v: Float| {
    Ok((*v.inner() as i64).into())
});

map_type!(into = Str, from = Float, |v: Float| {
    Ok(v.to_string().into())
});

map_type!(into = Array, from = Float, |v: Float| {
    Ok(vec![Value::from(v)].into())
});

map_type!(into = Object, from = Float, |v: Float| {
    let index = Value::from(Int::new(0));
    let value = Value::from(v);

    // Convert [index, value] into ObjectInner
    let map: ObjectInner = vec![(index, value)].into_iter().collect();

    Ok(map.into())
});
