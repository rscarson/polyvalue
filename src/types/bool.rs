//! `Bool` type
//!
//! This type wraps a `bool`. All other types can be successfully converted to a `Bool`:
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `true` or `false`
//!
use crate::{operations::*, types::*, Error, InnerValue, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::{hash::Hash, str::FromStr};

/// Subtype of `Value` that represents a boolean
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Bool(bool);
impl_value!(Bool, bool, |v: &Self| if *v.inner() {
    "true"
} else {
    "false"
});

impl Bool {
    /// Determine if a value is truthy (not empty or 0)
    pub fn is_truthy(value: &Value) -> bool {
        match value.inner() {
            InnerValue::Bool(v) => *v.inner(),
            InnerValue::Float(v) => *v.inner() != 0.0,
            InnerValue::U8(v) => *v.inner() != 0,
            InnerValue::I8(v) => *v.inner() != 0,
            InnerValue::U16(v) => *v.inner() != 0,
            InnerValue::I16(v) => *v.inner() != 0,
            InnerValue::U32(v) => *v.inner() != 0,
            InnerValue::I32(v) => *v.inner() != 0,
            InnerValue::U64(v) => *v.inner() != 0,
            InnerValue::I64(v) => *v.inner() != 0,
            InnerValue::Fixed(v) => *v != Fixed::zero(),
            InnerValue::Currency(v) => v.value() != &Fixed::zero(),
            InnerValue::String(v) => !v.is_empty(),
            InnerValue::Range(v) => v.start() != v.end(),
            InnerValue::Array(v) => !v.is_empty(),
            InnerValue::Object(v) => !v.is_empty(),
        }
    }
}

impl From<Bool> for Value {
    fn from(value: Bool) -> Self {
        Value::bool(value)
    }
}

impl From<Value> for Bool {
    fn from(value: Value) -> Self {
        match value.into_inner() {
            InnerValue::Bool(v) => v.into_inner(),
            InnerValue::Float(v) => v.into_inner() != 0.0,
            InnerValue::U8(v) => v.into_inner() != 0,
            InnerValue::I8(v) => v.into_inner() != 0,
            InnerValue::U16(v) => v.into_inner() != 0,
            InnerValue::I16(v) => v.into_inner() != 0,
            InnerValue::U32(v) => v.into_inner() != 0,
            InnerValue::I32(v) => v.into_inner() != 0,
            InnerValue::U64(v) => v.into_inner() != 0,
            InnerValue::I64(v) => v.into_inner() != 0,
            InnerValue::Fixed(v) => v != Fixed::zero(),
            InnerValue::Currency(v) => v.into_inner().into_value() != Fixed::zero(),
            InnerValue::String(v) => !v.is_empty(),
            InnerValue::Range(v) => v.start() != v.end(),
            InnerValue::Array(v) => !v.is_empty(),
            InnerValue::Object(v) => !v.is_empty(),
        }
        .into()
    }
}

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
map_type!(Range, Bool);

overload_operator!(Bool, arithmetic);
overload_operator!(Bool, bool_not);
overload_operator!(Bool, deref);

impl ArithmeticOperationExt for Bool {
    fn arithmetic_op(
        self,
        right: Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let (left, right) = (self.into_inner(), right.into_inner());
        let result = match operation {
            ArithmeticOperation::Add => left ^ right,
            ArithmeticOperation::Subtract => left ^ right,
            ArithmeticOperation::Multiply => left & right,
            ArithmeticOperation::Divide | ArithmeticOperation::Modulo => {
                if !right {
                    return Err(Error::Overflow);
                }

                left
            }
            ArithmeticOperation::Exponentiate => !right | left,
        };

        Ok(result.into())
    }

    fn arithmetic_neg(self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Ok((!self.inner()).into())
    }
}

impl BooleanOperationExt for Bool {
    fn boolean_op(self, right: Self, operation: BooleanOperation) -> Result<Value, Error> {
        let (left, right) = (self.into_inner(), right.into_inner());
        let result = match operation {
            BooleanOperation::And => left && right,
            BooleanOperation::Or => left || right,
            BooleanOperation::LT => !left & right,
            BooleanOperation::GT => left & !right,
            BooleanOperation::LTE => left <= right,
            BooleanOperation::GTE => left >= right,
            BooleanOperation::EQ => left == right,
            BooleanOperation::NEQ => left != right,
        };

        Ok(result.into())
    }

    fn boolean_not(self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Ok((!self.inner()).into())
    }
}

//
// Tests
//

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_arithmetic() {
        let result =
            Bool::arithmetic_op(Bool::from(true), Bool::from(true), ArithmeticOperation::Add)
                .unwrap();
        assert_eq!(result, Bool::from(false));
        let result = Bool::arithmetic_op(
            Bool::from(false),
            Bool::from(true),
            ArithmeticOperation::Add,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true));

        assert_eq!(
            Bool::arithmetic_neg(Bool::from(true)).unwrap(),
            Bool::from(false)
        );

        // division by 0 is error
        assert!(Bool::arithmetic_op(
            Bool::from(true),
            Bool::from(false),
            ArithmeticOperation::Divide
        )
        .is_err());

        assert_eq!(
            Bool::arithmetic_op(
                Bool::from(true),
                Bool::from(true),
                ArithmeticOperation::Divide
            )
            .unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::arithmetic_op(
                Bool::from(true),
                Bool::from(true),
                ArithmeticOperation::Subtract
            )
            .unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::arithmetic_op(
                Bool::from(true),
                Bool::from(true),
                ArithmeticOperation::Multiply
            )
            .unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::arithmetic_op(
                Bool::from(true),
                Bool::from(false),
                ArithmeticOperation::Multiply
            )
            .unwrap(),
            Bool::from(false)
        );

        // test that base-2 exponentiation holds
        assert_eq!(
            Bool::arithmetic_op(
                Bool::from(true),
                Bool::from(true),
                ArithmeticOperation::Exponentiate
            )
            .unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::arithmetic_op(
                Bool::from(true),
                Bool::from(false),
                ArithmeticOperation::Exponentiate
            )
            .unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::arithmetic_op(
                Bool::from(false),
                Bool::from(true),
                ArithmeticOperation::Exponentiate
            )
            .unwrap(),
            Bool::from(false)
        );
    }

    #[test]
    fn test_boolean_logic() {
        let result =
            Bool::boolean_op(Bool::from(true), Bool::from(true), BooleanOperation::And).unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result =
            Bool::boolean_op(Bool::from(true), Bool::from(false), BooleanOperation::And).unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result =
            Bool::boolean_op(Bool::from(true), Bool::from(false), BooleanOperation::Or).unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result =
            Bool::boolean_op(Bool::from(true), Bool::from(false), BooleanOperation::LT).unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result =
            Bool::boolean_op(Bool::from(true), Bool::from(false), BooleanOperation::GT).unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result =
            Bool::boolean_op(Bool::from(true), Bool::from(false), BooleanOperation::LTE).unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result =
            Bool::boolean_op(Bool::from(true), Bool::from(false), BooleanOperation::GTE).unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result =
            Bool::boolean_op(Bool::from(true), Bool::from(false), BooleanOperation::EQ).unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result =
            Bool::boolean_op(Bool::from(true), Bool::from(false), BooleanOperation::NEQ).unwrap();
        assert_eq!(result, Bool::from(true).into());

        assert_eq!(
            Bool::boolean_not(Bool::from(true)).unwrap(),
            Bool::from(false).into()
        );
    }

    #[test]
    fn test_to_string() {
        assert_eq!(Bool::from(true).to_string(), "true");
        assert_eq!(Bool::from(false).to_string(), "false");
    }

    #[test]
    fn test_from() {
        assert_eq!(Bool::from(true), Bool::from(true));
        assert_eq!(Bool::from(false), Bool::from(false));

        // Try-From other types
        assert_eq!(Bool::try_from(Value::from(1)).unwrap(), Bool::from(true));
        assert_eq!(Bool::try_from(Value::from(0)).unwrap(), Bool::from(false));

        assert_eq!(Bool::try_from(Value::from(1.0)).unwrap(), Bool::from(true));
        assert_eq!(Bool::try_from(Value::from(0.0)).unwrap(), Bool::from(false));

        assert_eq!(
            Bool::try_from(Value::from(Fixed::from_str("1.0").unwrap())).unwrap(),
            Bool::from(true)
        );
        assert_eq!(
            Bool::try_from(Value::from(Fixed::from_str("0.0").unwrap())).unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::try_from(Value::from("true")).unwrap(),
            Bool::from(true)
        );
        assert_eq!(Bool::try_from(Value::from("")).unwrap(), Bool::from(false));

        let array: Vec<Value> = vec![1.into(), 2.into(), 3.into()];
        assert_eq!(
            Bool::try_from(Value::from(array)).unwrap(),
            Bool::from(true)
        );
        let array: Vec<Value> = vec![];
        assert_eq!(
            Bool::try_from(Value::from(array)).unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::try_from(Value::try_from(vec![(1, 2)]).unwrap()).unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::try_from(Value::from(0..=10)).unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::try_from(Value::from(Currency::from_str("0.0").unwrap())).unwrap(),
            Bool::from(false)
        );

        assert_eq!(Bool::try_from(Value::from(1_u8)).unwrap(), Bool::from(true));
        assert_eq!(
            Bool::try_from(Value::from(0_u8)).unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::try_from(Value::from(1_u16)).unwrap(),
            Bool::from(true)
        );
        assert_eq!(
            Bool::try_from(Value::from(0_u16)).unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::try_from(Value::from(1_u32)).unwrap(),
            Bool::from(true)
        );
        assert_eq!(
            Bool::try_from(Value::from(0_u32)).unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::try_from(Value::from(1_u64)).unwrap(),
            Bool::from(true)
        );
        assert_eq!(
            Bool::try_from(Value::from(0_u64)).unwrap(),
            Bool::from(false)
        );

        assert_eq!(Bool::try_from(Value::from(1_i8)).unwrap(), Bool::from(true));
        assert_eq!(
            Bool::try_from(Value::from(0_i8)).unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::try_from(Value::from(1_i16)).unwrap(),
            Bool::from(true)
        );
        assert_eq!(
            Bool::try_from(Value::from(0_i16)).unwrap(),
            Bool::from(false)
        );

        assert_eq!(Bool::try_from(Value::i32(1_i32)).unwrap(), Bool::from(true));
        assert_eq!(
            Bool::try_from(Value::i32(0_i32)).unwrap(),
            Bool::from(false)
        );

        assert_eq!(Bool::try_from(Value::i64(1_i32)).unwrap(), Bool::from(true));
        assert_eq!(
            Bool::try_from(Value::i64(0_i64)).unwrap(),
            Bool::from(false)
        );
    }

    #[test]
    fn test_parse() {
        assert_eq!("true".parse::<Bool>().unwrap(), Bool::from(true));
        assert_eq!("false".parse::<Bool>().unwrap(), Bool::from(false));
        assert!("".parse::<Bool>().is_err());
        assert!("1".parse::<Bool>().is_err());
        assert!("0".parse::<Bool>().is_err());
    }
}
