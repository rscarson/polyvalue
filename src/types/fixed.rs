//! Fixed-point decimal type
//!
//! This type is a wrapper around [`fpdec::Decimal`](https://docs.rs/fpdec/0.5.0/fpdec/struct.Decimal.html).
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use std::str::FromStr;

use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use fpdec::{CheckedAdd, CheckedDiv, CheckedMul, CheckedRem, CheckedSub, Decimal, Round};
use serde::{Deserialize, Serialize};

/// Inner type of `Fixed`
pub type FixedInner = Decimal;

/// Subtype of `Value` that represents a fixed-point decimal
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, Default, Debug)]
pub struct Fixed(FixedInner);
impl_value!(Fixed, FixedInner, |v: &Self| v.inner().to_string());

map_value!(
    from = Fixed,
    handle_into = |v: Fixed| Value::Fixed(v),
    handle_from = |v: Value| match v {
        Value::Fixed(v) => Ok(v),
        Value::Int(v) => {
            let p = *v.inner();
            let p: Decimal = p.into();
            Ok(Fixed::from(p))
        }
        Value::Float(v) => {
            let p = *v.inner();
            let p = Decimal::try_from(p)?;

            // Ok this is an ugly hack. A bad bad hack.
            // It is slow and inefficient, BUT it works.
            // It is intended to fix floating point errors by leveraging the fact that
            // f64 strings somehow have the correct precision.

            // Todo: find a better way to do this
            let intended_precision = v
                .to_string()
                .split(".")
                .last()
                .map(|s| s.len())
                .unwrap_or(0);
            let p = p.round(intended_precision as i8);

            Ok(Fixed::from(p))
        }
        Value::Currency(v) => {
            Ok(v.inner().value().clone())
        }
        Value::Bool(v) => {
            if *v.inner() {
                Ok(Fixed::from(Decimal::ONE))
            } else {
                Ok(Fixed::from(Decimal::ZERO))
            }
        }
        Value::String(_) => {
            Err(Error::ValueConversion {
                src_type: ValueType::String,
                dst_type: ValueType::Fixed,
            })
        }
        Value::Array(v) => {
            if v.inner().len() == 1 {
                let v = v.inner()[0].clone();
                Fixed::try_from(v)
            } else {
                Err(Error::ValueConversion {
                    src_type: ValueType::Array,
                    dst_type: ValueType::Fixed,
                })
            }
        }
        Value::Object(v) => {
            if v.inner().len() == 1 {
                let v = v.inner().values().next().unwrap().clone();
                Fixed::try_from(v)
            } else {
                Err(Error::ValueConversion {
                    src_type: ValueType::Object,
                    dst_type: ValueType::Fixed,
                })
            }
        }
    }
);

map_type!(Array, Fixed);
map_type!(Object, Fixed);
map_type!(Int, Fixed);
map_type!(Float, Fixed);
map_type!(Currency, Fixed);
map_type!(Str, Fixed);

//
// Trait implementations
//

impl FromStr for Fixed {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.replace(",", "").parse::<FixedInner>()?.into())
    }
}

impl std::hash::Hash for Fixed {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Float::try_from(Value::from(self.clone()))
            .unwrap()
            .hash(state)
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
                let left = Float::try_from(Value::from(left.clone()))?;
                let right = Float::try_from(Value::from(right.clone()))?;

                let result = Float::arithmetic_op(&left, &right, operation)?;
                Some(Fixed::try_from(Value::from(result))?.inner().clone())
            }
            ArithmeticOperation::Negate => Some(-left_),
        }
        .ok_or(Error::Overflow)?;

        Ok(result.into())
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Fixed::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }
}

impl BooleanOperationExt for Fixed {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => {
                *left.inner() != Decimal::ZERO && *right.inner() != Decimal::ZERO
            }
            BooleanOperation::Or => {
                *left.inner() != Decimal::ZERO || *right.inner() != Decimal::ZERO
            }

            BooleanOperation::LT => *left.inner() < *right.inner(),
            BooleanOperation::GT => *left.inner() > *right.inner(),
            BooleanOperation::LTE => *left.inner() <= *right.inner(),
            BooleanOperation::GTE => *left.inner() >= *right.inner(),
            BooleanOperation::EQ => *left.inner() == *right.inner(),
            BooleanOperation::NEQ => *left.inner() != *right.inner(),
            BooleanOperation::Not => *left.inner() == Decimal::ZERO,
        };

        Ok(result.into())
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Fixed::boolean_op(self, &self.clone(), BooleanOperation::Not)
    }
}

//
// Tests
//

#[cfg(test)]
mod tests {
    use fpdec::Dec;

    use super::*;

    #[test]
    fn test_arithmetic() {
        assert_eq!(
            Fixed::arithmetic_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Add
            )
            .unwrap(),
            Fixed::from_str("15").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Subtract
            )
            .unwrap(),
            Fixed::from_str("5").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Multiply
            )
            .unwrap(),
            Fixed::from_str("50").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Divide
            )
            .unwrap(),
            Fixed::from_str("2").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Modulo
            )
            .unwrap(),
            Fixed::from_str("0").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Exponentiate
            )
            .unwrap(),
            Fixed::from_str("100000").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("0").unwrap(),
                ArithmeticOperation::Negate
            )
            .unwrap(),
            Fixed::from_str("-10").unwrap()
        );
    }

    #[test]
    fn test_boolean_logic() {
        assert_eq!(
            Fixed::boolean_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                BooleanOperation::And
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                BooleanOperation::Or
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                BooleanOperation::LT
            )
            .unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Fixed::boolean_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                BooleanOperation::GT
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                BooleanOperation::LTE
            )
            .unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Fixed::boolean_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                BooleanOperation::GTE
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                BooleanOperation::EQ
            )
            .unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Fixed::boolean_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("5").unwrap(),
                BooleanOperation::NEQ
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_op(
                &Fixed::from_str("10").unwrap(),
                &Fixed::from_str("0").unwrap(),
                BooleanOperation::Not
            )
            .unwrap(),
            Value::from(false)
        );
    }

    #[test]
    fn test_to_string() {
        assert_eq!(Fixed::from_str("10.0").unwrap().to_string(), "10.0");
        assert_eq!(Fixed::from_str("-0.0").unwrap().to_string(), "0.0");
        assert_eq!(Fixed::from_str("10").unwrap().to_string(), "10");
    }

    #[test]
    fn test_from() {
        assert_eq!(
            Value::from(Fixed::from_str("10.0").unwrap()),
            Value::Fixed(Fixed::from_str("10.0").unwrap())
        );

        assert_eq!(
            Fixed::try_from(Value::from(1)).unwrap(),
            Fixed::from_str("1").unwrap()
        );

        assert_eq!(
            Fixed::try_from(Value::from(1.0)).unwrap(),
            Fixed::from_str("1.0").unwrap()
        );

        assert_eq!(
            Fixed::try_from(Value::from(Currency::from_fixed(
                Fixed::from_str("1.0").unwrap()
            )))
            .unwrap(),
            Fixed::from_str("1.0").unwrap()
        );

        assert_eq!(
            Fixed::try_from(Value::from(true)).unwrap(),
            Fixed::from_str("1").unwrap()
        );

        // From str should fail
        assert!(Fixed::try_from(Value::from("1")).is_err());

        // from single element array
        assert_eq!(
            Fixed::try_from(Value::from(vec![Value::from(1)])).unwrap(),
            Fixed::from_str("1").unwrap()
        );

        // from single element object
        assert_eq!(
            Fixed::try_from(Value::from(vec![(Value::from("a"), Value::from(1))])).unwrap(),
            Fixed::from_str("1").unwrap()
        );

        // from multiple element array should fail
        assert!(Fixed::try_from(Value::from(vec![Value::from(1), Value::from(2)])).is_err());

        // from multiple element object should fail
        assert!(Fixed::try_from(Value::from(vec![
            (Value::from("a"), Value::from(1)),
            (Value::from("b"), Value::from(2))
        ]))
        .is_err());
    }

    #[test]
    fn test_parse() {
        assert_eq!(Fixed::from_str("10.0").unwrap(), Fixed::from(Dec!(10.0)));
        assert_eq!(Fixed::from_str("10").unwrap(), Fixed::from(Dec!(10)));
        assert_eq!(Fixed::from_str("-10").unwrap(), Fixed::from(Dec!(-10)));
    }
}
