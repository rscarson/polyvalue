use crate::{operations::*, types::*, Error, Value, ValueTrait};
use fpdec::Decimal;
use serde::{Deserialize, Serialize};
use std::hash::Hash;

/// Subtype of `Value` that represents a boolean
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Bool(bool);
impl_value!(Bool, bool);

map_value!(
    from = Bool,
    handle_into = |v: Bool| Value::Bool(v),
    handle_from = |v: Value| match v {
        Value::Bool(v) => Ok(v),
        Value::Int(v) => v.try_into(),
        Value::Float(v) => v.try_into(),
        Value::Fixed(v) => v.try_into(),
        Value::Currency(v) => v.try_into(),
        Value::String(v) => v.try_into(),
        Value::Array(v) => v.try_into(),
        Value::Object(v) => v.try_into(),
    }
);

impl ArithmeticOperationExt for Bool {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = Int::try_from(left.clone())?;
        let right = Int::try_from(right.clone())?;
        let result = Int::arithmetic_op(&left, &right, operation)?;
        Ok(result.try_into()?)
    }
}

//
// Conversion from other types
//

fn map_from<T>(v: Bool, if_: T, nif_: T) -> Result<T, Error> {
    Ok(if v.into() { if_ } else { nif_ })
}

map_type!(into = Str, from = Bool, |v| {
    map_from::<Str>(v, "true".to_string().into(), "false".to_string().into())
});

map_type!(into = Int, from = Bool, |v| {
    map_from::<Int>(v, 1.into(), 0.into())
});

map_type!(into = Float, from = Bool, |v| {
    map_from::<Float>(v, 1.0.into(), 0.0.into())
});

map_type!(into = Fixed, from = Bool, |v| {
    map_from::<Fixed>(v, Decimal::ONE.into(), Decimal::ZERO.into())
});

map_type!(into = Currency, from = Bool, |v| {
    map_from::<Currency>(
        v,
        Currency::without_symbol(Decimal::ONE.into()),
        Currency::without_symbol(Decimal::ZERO.into()),
    )
});

map_type!(into = Array, from = Bool, |v: Bool| {
    Ok(vec![Value::from(v)].into())
});

map_type!(into = Object, from = Bool, |v: Bool| {
    let index = Value::from(Int::new(0));
    let value = Value::from(v);

    // Convert [index, value] into ObjectInner
    let map: ObjectInner = vec![(index, value)].into_iter().collect();

    Ok(map.into())
});
