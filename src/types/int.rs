use std::str::FromStr;

use crate::{operations::*, types::*, Error, Value, ValueTrait};
use serde::{Deserialize, Serialize};

/// Inner type of `Int`
pub type IntInner = i64;

/// Subtype of `Value` that represents an integer
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Int(IntInner);
impl_value!(Int, IntInner);

map_value!(
    from = Int,
    handle_into = |v: Int| Value::Int(v),
    handle_from = |v: Value| match v {
        Value::Int(v) => Ok(v),
        Value::Fixed(v) => v.try_into(),
        Value::Float(v) => v.try_into(),
        Value::Currency(v) => v.try_into(),
        Value::Bool(v) => v.try_into(),
        Value::String(v) => v.try_into(),
        Value::Array(v) => v.try_into(),
        Value::Object(v) => v.try_into(),
    }
);

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

//
// Conversion from other types
//

map_type!(into = Bool, from = Int, |v: Int| {
    Ok((*v.inner() != 0).into())
});

map_type!(into = Fixed, from = Int, |v: Int| {
    Fixed::from_str(&v.to_string())
});

map_type!(into = Float, from = Int, |v: Int| {
    Ok((*v.inner() as f64).into())
});

map_type!(into = Currency, from = Int, |v: Int| {
    Ok(Currency::without_symbol(v.try_into()?))
});

map_type!(into = Str, from = Int, |v: Int| {
    Ok(v.to_string().into())
});

map_type!(into = Array, from = Int, |v: Int| {
    Ok(vec![Value::from(v)].into())
});

map_type!(into = Object, from = Int, |v: Int| {
    let index = Value::from(Int::new(0));
    let value = Value::from(v);

    // Convert [index, value] into ObjectInner
    let map: ObjectInner = vec![(index, value)].into_iter().collect();

    Ok(map.into())
});
