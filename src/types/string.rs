use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};

/// Subtype of `Value` that represents a string
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Str(String);
impl_value!(Str, String);

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
        Value::Bool(v) => v.try_into(),
        Value::Fixed(v) => v.try_into(),
        Value::Float(v) => v.try_into(),
        Value::Currency(v) => v.try_into(),
        Value::Int(v) => v.try_into(),
        Value::Array(v) => v.try_into(),
        Value::Object(v) => v.try_into(),
    }
);

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

impl IndexingOperationExt for Str {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        let chars = self
            .inner()
            .chars()
            .map(|c| Value::from(c.to_string()))
            .collect::<Vec<_>>();
        let chars = Value::from(chars);
        chars.get_index(index)
    }

    fn set_index(&mut self, index: &Value, value: Value) -> Result<(), crate::Error> {
        let chars = self
            .inner()
            .chars()
            .map(|c| Value::from(c.to_string()))
            .collect::<Vec<_>>();
        let mut chars = Value::from(chars);
        chars.set_index(index, value)?;

        let str = Array::try_from(chars)?
            .inner()
            .iter()
            .map(|v| v.to_string())
            .collect::<String>();
        self.inner_mut().clear();
        self.inner_mut().push_str(str.as_str());
        Ok(())
    }
}

//
// Conversion from other types
//

map_type!(into = Bool, from = Str, |v: Str| {
    Ok((!v.inner().is_empty()).into())
});

map_type!(into = Fixed, from = Str, |_: Str| {
    Err(Error::ValueConversion {
        src_type: ValueType::String,
        dst_type: ValueType::Fixed,
    })
});

map_type!(into = Float, from = Str, |_: Str| {
    Err(Error::ValueConversion {
        src_type: ValueType::String,
        dst_type: ValueType::Float,
    })
});

map_type!(into = Currency, from = Str, |_: Str| {
    Err(Error::ValueConversion {
        src_type: ValueType::String,
        dst_type: ValueType::Currency,
    })
});

map_type!(into = Int, from = Str, |_: Str| {
    Err(Error::ValueConversion {
        src_type: ValueType::String,
        dst_type: ValueType::Int,
    })
});

map_type!(into = Array, from = Str, |v: Str| {
    Ok(vec![Value::from(v)].into())
});

map_type!(into = Object, from = Str, |v: Str| {
    let index = Value::from(Int::new(0));
    let value = Value::from(v);

    // Convert [index, value] into ObjectInner
    let map: ObjectInner = vec![(index, value)].into_iter().collect();

    Ok(map.into())
});
