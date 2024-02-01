//! `Bool` type
//!
//! This type wraps a `bool`. All other types can be successfully converted to a `Bool`:
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `true` or `false`
//!
use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
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

map_value!(
    from = Bool,
    handle_into = Value::Bool,
    handle_from = |v: Value| match v {
        Value::Range(_) => Self::try_from(v.as_a::<Array>()?),
        Value::Bool(v) => Ok(v),

        Value::U8(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }

        Value::U16(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }

        Value::U32(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }

        Value::U64(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }

        Value::I8(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }

        Value::I16(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }

        Value::I32(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }

        Value::I64(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }

        Value::Float(v) => {
            Ok(Bool::from(*v.inner() != 0.0))
        }
        Value::Fixed(v) => {
            Ok(Bool::from(v != Fixed::zero()))
        }
        Value::Currency(v) => {
            Ok(Bool::from(v.inner().value() == &Fixed::zero()))
        }
        Value::String(v) => {
            Ok(Bool::from(!v.inner().is_empty()))
        }
        Value::Array(v) => {
            Ok(Bool::from(!v.inner().is_empty()))
        }
        Value::Object(v) => {
            Ok(Bool::from(!v.inner().is_empty()))
        }
    }
);

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
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = *left.inner();
        let right = *right.inner();
        let result = match operation {
            ArithmeticOperation::Add => left ^ right,
            ArithmeticOperation::Subtract => left ^ right,
            ArithmeticOperation::Multiply => left & right,
            ArithmeticOperation::Divide | ArithmeticOperation::Modulo => {
                if right == false {
                    return Err(Error::Overflow);
                }

                left
            }
            ArithmeticOperation::Exponentiate => !right | left,
            ArithmeticOperation::Negate => !left,
        };

        Ok(result.into())
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Bool::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }

    fn is_operator_supported(&self, _other: &Self, _: ArithmeticOperation) -> bool {
        true
    }
}

impl BooleanOperationExt for Bool {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => *left.inner() && *right.inner(),
            BooleanOperation::Or => *left.inner() || *right.inner(),
            BooleanOperation::LT => !(*left.inner()) & *right.inner(),
            BooleanOperation::GT => *left.inner() & !(*right.inner()),
            BooleanOperation::LTE => *left.inner() <= *right.inner(),
            BooleanOperation::GTE => *left.inner() >= *right.inner(),
            BooleanOperation::EQ => *left.inner() == *right.inner(),
            BooleanOperation::NEQ => *left.inner() != *right.inner(),
            BooleanOperation::Not => !*left.inner(),
        };

        Ok(result.into())
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Bool::boolean_op(self, &self.clone(), BooleanOperation::Not)
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
        let result = Bool::arithmetic_op(
            &Bool::from(true),
            &Bool::from(true),
            ArithmeticOperation::Add,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false));
        let result = Bool::arithmetic_op(
            &Bool::from(false),
            &Bool::from(true),
            ArithmeticOperation::Add,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true));

        assert_eq!(
            Bool::arithmetic_neg(&Bool::from(true)).unwrap(),
            Bool::from(false)
        );

        // division by 0 is error
        assert!(Bool::arithmetic_op(
            &Bool::from(true),
            &Bool::from(false),
            ArithmeticOperation::Divide
        )
        .is_err());

        assert_eq!(
            Bool::arithmetic_op(
                &Bool::from(true),
                &Bool::from(true),
                ArithmeticOperation::Divide
            )
            .unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::arithmetic_op(
                &Bool::from(true),
                &Bool::from(true),
                ArithmeticOperation::Subtract
            )
            .unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::arithmetic_op(
                &Bool::from(true),
                &Bool::from(true),
                ArithmeticOperation::Multiply
            )
            .unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::arithmetic_op(
                &Bool::from(true),
                &Bool::from(false),
                ArithmeticOperation::Multiply
            )
            .unwrap(),
            Bool::from(false)
        );

        // test that base-2 exponentiation holds
        assert_eq!(
            Bool::arithmetic_op(
                &Bool::from(true),
                &Bool::from(true),
                ArithmeticOperation::Exponentiate
            )
            .unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::arithmetic_op(
                &Bool::from(true),
                &Bool::from(false),
                ArithmeticOperation::Exponentiate
            )
            .unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::arithmetic_op(
                &Bool::from(false),
                &Bool::from(true),
                ArithmeticOperation::Exponentiate
            )
            .unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::is_operator_supported(
                &Bool::from(true),
                &Bool::from(true),
                ArithmeticOperation::Add
            ),
            true
        );
    }

    #[test]
    fn test_boolean_logic() {
        let result =
            Bool::boolean_op(&Bool::from(true), &Bool::from(true), BooleanOperation::And).unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result =
            Bool::boolean_op(&Bool::from(true), &Bool::from(false), BooleanOperation::And).unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result =
            Bool::boolean_op(&Bool::from(true), &Bool::from(false), BooleanOperation::Or).unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result =
            Bool::boolean_op(&Bool::from(true), &Bool::from(false), BooleanOperation::LT).unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result =
            Bool::boolean_op(&Bool::from(true), &Bool::from(false), BooleanOperation::GT).unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result =
            Bool::boolean_op(&Bool::from(true), &Bool::from(false), BooleanOperation::LTE).unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result =
            Bool::boolean_op(&Bool::from(true), &Bool::from(false), BooleanOperation::GTE).unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result =
            Bool::boolean_op(&Bool::from(true), &Bool::from(false), BooleanOperation::EQ).unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result =
            Bool::boolean_op(&Bool::from(true), &Bool::from(false), BooleanOperation::NEQ).unwrap();
        assert_eq!(result, Bool::from(true).into());

        assert_eq!(
            Bool::boolean_not(&Bool::from(true)).unwrap(),
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
            Bool::try_from(Value::try_from(vec![(1.into(), 2.into())]).unwrap()).unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::try_from(Value::from(0..=10)).unwrap(),
            Bool::from(true)
        );

        assert_eq!(
            Bool::try_from(Value::from(Currency::from_str("0.0").unwrap())).unwrap(),
            Bool::from(true)
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

        assert_eq!(
            Bool::try_from(Value::I32(I32::new(1_i32))).unwrap(),
            Bool::from(true)
        );
        assert_eq!(
            Bool::try_from(Value::I32(I32::new(0_i32))).unwrap(),
            Bool::from(false)
        );

        assert_eq!(
            Bool::try_from(Value::I64(I64::new(1_i64))).unwrap(),
            Bool::from(true)
        );
        assert_eq!(
            Bool::try_from(Value::I64(I64::new(0_i64))).unwrap(),
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
