//! `Bool` type
//!
//! This type wraps a `bool`. All other types can be successfully converted to a `Bool`:
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `true` or `false`
//!
use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use fpdec::Decimal;
use serde::{Deserialize, Serialize};
use std::{hash::Hash, str::FromStr};

/// Subtype of `Value` that represents a boolean
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Bool(bool);
impl_value!(Bool, bool, |v: &Self| if *v.inner() {
    "true"
} else {
    "false"
});

map_value!(
    from = Bool,
    handle_into = |v: Bool| Value::Bool(v),
    handle_from = |v: Value| match v {
        Value::Bool(v) => Ok(v),
        Value::Int(v) => {
            Ok(Bool::from(*v.inner() != 0))
        }
        Value::Float(v) => {
            Ok(Bool::from(*v.inner() != 0.0))
        }
        Value::Fixed(v) => {
            Ok(Bool::from(*v.inner() != Decimal::ZERO))
        }
        Value::Currency(v) => {
            Ok(Bool::from(*v.inner().value().inner() == Decimal::ZERO).into())
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

impl ArithmeticOperationExt for Bool {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = Int::try_from(Value::from(left.clone()))?;
        let right = Int::try_from(Value::from(right.clone()))?;
        let result = Int::arithmetic_op(&left, &right, operation)?;
        Ok(Value::from(result).try_into()?)
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Bool::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }
}

impl BooleanOperationExt for Bool {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => *left.inner() && *right.inner(),
            BooleanOperation::Or => *left.inner() || *right.inner(),
            BooleanOperation::LT => *left.inner() < *right.inner(),
            BooleanOperation::GT => *left.inner() > *right.inner(),
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
        assert_eq!(result, Bool::from(true));
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
            Bool::try_from(Value::from(Decimal::from_str("1.0").unwrap())).unwrap(),
            Bool::from(true)
        );
        assert_eq!(
            Bool::try_from(Value::from(Decimal::from_str("0.0").unwrap())).unwrap(),
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
