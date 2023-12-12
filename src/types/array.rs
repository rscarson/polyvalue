use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::hash::Hash;

/// Inner type used for array storage
pub type ArrayInner = Vec<Value>;

/// Subtype of `Value` that represents an array
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Array(ArrayInner);
impl_value!(Array, ArrayInner);

map_value!(
    from = Array,
    handle_into = |v: Array| Value::Array(v),
    handle_from = |v: Value| match v {
        Value::Array(v) => Ok(v),
        Value::Int(v) => v.try_into(),
        Value::Float(v) => v.try_into(),
        Value::Fixed(v) => v.try_into(),
        Value::Currency(v) => v.try_into(),
        Value::Bool(v) => v.try_into(),
        Value::String(v) => v.try_into(),
        Value::Object(v) => v.try_into(),
    }
);

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
// Conversion from other types
//

fn map_from<T>(v: Array) -> Result<T, Error>
where
    T: TryFrom<Value, Error = Error>,
{
    if v.inner().len() == 1 {
        T::try_from(v.inner()[0].clone())
    } else {
        Err(Error::ValueConversion {
            src_type: ValueType::Array,
            dst_type: ValueType::Bool,
        })
    }
}

map_type!(into = Bool, from = Array, |v: Array| map_from::<Bool>(v));
map_type!(into = Fixed, from = Array, |v: Array| map_from::<Fixed>(v));
map_type!(into = Float, from = Array, |v: Array| map_from::<Float>(v));
map_type!(into = Int, from = Array, |v: Array| map_from::<Int>(v));
map_type!(
    into = Currency,
    from = Array,
    |v: Array| map_from::<Currency>(v)
);

map_type!(into = Str, from = Array, |v: Array| {
    Ok(format!(
        "[{}]",
        v.inner()
            .iter()
            .map(|v| format!("{}", v))
            .collect::<Vec<String>>()
            .join(", ")
    )
    .into())
});

map_type!(into = Object, from = Array, |v: Array| {
    let mut obj = HashMap::<Value, Value>::new();
    for (i, v) in v.inner().iter().enumerate() {
        let index: Int = (i as i64).into();
        let index = Value::from(index);
        obj.insert(index, v.clone());
    }
    Ok(obj.into())
});

//
// Tests
//

#[cfg(test)]
mod test {
    use super::*;
    use fpdec::Decimal;

    #[test]
    fn test_primitive() {
        let inner: ArrayInner = vec![Int::new(1).into(), Int::new(2).into()];
        let outer: Array = inner.clone().into();
        let inner2: ArrayInner = outer.into();
        assert_eq!(inner, inner2);
    }

    #[test]
    fn test_value() {
        let array = Array::new(vec![Int::new(1).into(), Int::new(2).into()]);
        let value: Value = array.clone().into();
        assert_eq!(value, Value::Array(array));

        let bool = Value::from(Bool::new(true));
        let array = Array::try_from(bool.clone()).unwrap();
        assert_eq!(array.inner(), &[bool]);

        let fixed = Value::from(Fixed::new(Decimal::ONE));
        let array = Array::try_from(fixed.clone()).unwrap();
        assert_eq!(array.inner(), &[fixed]);

        let float = Value::from(Float::new(1.0));
        let array = Array::try_from(float.clone()).unwrap();
        assert_eq!(array.inner(), &[float]);

        let int = Value::from(Int::new(1));
        let array = Array::try_from(int.clone()).unwrap();
        assert_eq!(array.inner(), &[int]);

        let string = Value::from(Str::from("1"));
        let array = Array::try_from(string.clone()).unwrap();
        assert_eq!(array.inner(), &[string]);

        let object = Value::from(Object::new(HashMap::new()));
        let array = Array::try_from(object.clone()).unwrap();
        assert_eq!(array.inner(), &[object]);

        let array = Array::new(vec![Int::new(1).into(), Int::new(2).into()]);
        let value: Value = array.clone().into();
        assert_eq!(value, Value::Array(array));
    }

    #[test]
    fn test_types() {
        assert_eq!(
            Array::try_from(Bool::new(true)).unwrap(),
            Array::new(vec![Bool::new(true).into()]),
        );

        assert_eq!(
            Array::try_from(Fixed::new(Decimal::ONE)).unwrap(),
            Array::new(vec![Fixed::new(Decimal::ONE).into()]),
        );

        assert_eq!(
            Array::try_from(Float::new(1.0)).unwrap(),
            Array::new(vec![Float::new(1.0).into()]),
        );

        assert_eq!(
            Array::try_from(Int::new(1)).unwrap(),
            Array::new(vec![Int::new(1).into()]),
        );

        assert_eq!(
            Array::try_from(Str::from("1")).unwrap(),
            Array::new(vec![Str::from("1").into()]),
        );

        let mut obj = HashMap::<Value, Value>::new();
        obj.insert(Value::from(Int::new(0)), Value::from(Int::new(1)));
        obj.insert(Value::from(Int::new(1)), Value::from(Int::new(2)));
        assert_eq!(
            Array::try_from(Object::new(obj)).unwrap(),
            Array::new(vec![Int::new(1).into(), Int::new(2).into()]),
        );
    }
}
