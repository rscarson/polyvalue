use std::str::FromStr;

use crate::{operations::*, types::*, Error, Value, ValueTrait};
use fpdec::{CheckedAdd, CheckedDiv, CheckedMul, CheckedRem, CheckedSub, Decimal};
use serde::{Deserialize, Serialize};

/// Inner type of `Fixed`
pub type FixedInner = Decimal;

/// Subtype of `Value` that represents a fixed-point decimal
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, Default)]
pub struct Fixed(FixedInner);
impl_value!(Fixed, FixedInner);

map_value!(
    from = Fixed,
    handle_into = |v: Fixed| Value::Fixed(v),
    handle_from = |v: Value| match v {
        Value::Fixed(v) => Ok(v),
        Value::Int(v) => v.try_into(),
        Value::Float(v) => v.try_into(),
        Value::Currency(v) => v.try_into(),
        Value::Bool(v) => v.try_into(),
        Value::String(v) => v.try_into(),
        Value::Array(v) => v.try_into(),
        Value::Object(v) => v.try_into(),
    }
);

//
// Trait implementations
//

impl FromStr for Fixed {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.parse::<FixedInner>()?.into())
    }
}

impl std::hash::Hash for Fixed {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Float::try_from(self.clone()).unwrap().hash(state)
    }
}

impl ArithmeticOperationExt for Fixed {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left_ = left.inner().clone();
        let right_ = right.inner().clone();

        let result = match operation {
            ArithmeticOperation::Add => left_.checked_add(right_),
            ArithmeticOperation::Subtract => left_.checked_sub(right_),
            ArithmeticOperation::Multiply => left_.checked_mul(right_),
            ArithmeticOperation::Divide => left_.checked_div(right_),
            ArithmeticOperation::Modulo => left_.checked_rem(right_),
            ArithmeticOperation::Exponentiate => {
                // Convert to floats
                let left = Float::try_from(left.clone())?;
                let right = Float::try_from(right.clone())?;

                let result = Float::arithmetic_op(&left, &right, operation)?;
                Some(Fixed::try_from(result)?.inner().clone())
            }
            ArithmeticOperation::Negate => Some(-left_),
        }
        .ok_or(Error::Overflow)?;

        Ok(result.into())
    }
}

//
// Conversion from other types
//

map_type!(into = Bool, from = Fixed, |v: Fixed| {
    Ok((*v.inner() != FixedInner::ZERO).into())
});

map_type!(into = Float, from = Fixed, |v: Fixed| {
    Float::from_str(&v.to_string())
});

map_type!(into = Int, from = Fixed, |v: Fixed| {
    Ok((v.inner().trunc().coefficient() as i64).into())
});

map_type!(into = Currency, from = Fixed, |v: Fixed| {
    Ok(Currency::without_symbol(v).into())
});

map_type!(into = Str, from = Fixed, |v: Fixed| {
    Ok(v.to_string().into())
});

map_type!(into = Array, from = Fixed, |v: Fixed| {
    Ok(vec![v.into()].into())
});

map_type!(into = Object, from = Fixed, |v: Fixed| {
    let index = Value::from(Int::new(0));
    let value = Value::from(v);

    // Convert [index, value] into ObjectInner
    let map: ObjectInner = vec![(index, value)].into_iter().collect();

    Ok(map.into())
});
