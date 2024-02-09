//! Fixed-point decimal type
//!
//! This type is a wrapper around [`fpdec::Decimal`](https://docs.rs/fpdec/0.5.0/fpdec/struct.Decimal.html).
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use std::str::FromStr;

use crate::{
    inner_fixed::BoxedDecimal, operations::*, types::*, Error, InnerValue, Value, ValueTrait,
    ValueType,
};
use fpdec::{CheckedAdd, CheckedDiv, CheckedMul, CheckedRem, CheckedSub, Dec, Decimal, Round};
use serde::{Deserialize, Serialize};

/// Inner type of `Fixed`
pub type FixedInner = BoxedDecimal;

/// Subtype of `Value` that represents a fixed-point decimal
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Serialize, Deserialize, Default)]
pub struct Fixed(FixedInner);
impl_value!(Fixed, FixedInner, |v: &Self| (*v.inner()).to_string());

impl From<Decimal> for Fixed {
    fn from(value: Decimal) -> Self {
        Self::new(BoxedDecimal::from(value))
    }
}

impl Fixed {
    /// The value of Decimal::ZERO
    pub fn zero() -> Self {
        Self::new(BoxedDecimal::from(Decimal::ZERO))
    }

    /// The value of Decimal::ONE
    pub fn one() -> Self {
        Self::new(BoxedDecimal::from(Decimal::ONE))
    }

    /// Type-same checked exponentiation for fixed-point decimals
    pub fn checked_pow(&self, exp: &Self) -> Option<Self> {
        // We can use the fact that a**b == e**(b * ln(a))
        let a = *self.inner().clone();
        let b = *exp.inner().clone();

        // Approximate ln(a) using the taylor series
        let a_s1 = a.checked_sub(Dec!(1))?;
        let mut ln_a_mul = a_s1.clone();
        let mut ln_a = a_s1.clone();
        let mut multiplier = Dec!(-1);
        for i in 2..=10 {
            ln_a_mul = ln_a_mul.checked_mul(a_s1)?;
            let factor = ln_a_mul.checked_div(Decimal::from(i))?;
            let factor = factor.checked_mul(multiplier)?;

            ln_a = ln_a.checked_add(factor)?;
            multiplier = multiplier.checked_mul(Dec!(-1))?;
        }

        // Finally we approximate e**(b * ln(a)) using the taylor series
        let mut b_ln_a = b.checked_mul(ln_a)?;
        let mut e_b_ln_a = Dec!(1).checked_add(b_ln_a)?;
        let mut divisor = Dec!(1);
        for i in 2..=10 {
            divisor = divisor.checked_mul(Decimal::from(i))?;
            b_ln_a = b_ln_a.checked_mul(b_ln_a)?;
            let factor = b_ln_a.checked_div(divisor)?;
            e_b_ln_a = e_b_ln_a.checked_add(factor)?;
        }

        Some(Self::new(BoxedDecimal::from(e_b_ln_a)))
    }
}

map_value!(
    from = Fixed,
    handle_into = Value::fixed,
    handle_from = |v: Value| match v.inner() {
        InnerValue::Range(_) => Self::try_from(v.as_a::<Array>()?),
        InnerValue::Fixed(v) => Ok(v.clone()),

        InnerValue::U8(v) => {
            let p = *v.inner();
            let p: Decimal = p.into();
            Ok(Fixed::from(p))
        }
        InnerValue::U16(v) => {
            let p = *v.inner();
            let p: Decimal = p.into();
            Ok(Fixed::from(p))
        }
        InnerValue::U32(v) => {
            let p = *v.inner();
            let p: Decimal = p.into();
            Ok(Fixed::from(p))
        }
        InnerValue::U64(v) => {
            let p = *v.inner();
            let p: Decimal = p.into();
            Ok(Fixed::from(p))
        }
        InnerValue::I8(v) => {
            let p = *v.inner();
            let p: Decimal = p.into();
            Ok(Fixed::from(p))
        }
        InnerValue::I16(v) => {
            let p = *v.inner();
            let p: Decimal = p.into();
            Ok(Fixed::from(p))
        }
        InnerValue::I32(v) => {
            let p = *v.inner();
            let p: Decimal = p.into();
            Ok(Fixed::from(p))
        }
        InnerValue::I64(v) => {
            let p = *v.inner();
            let p: Decimal = p.into();
            Ok(Fixed::from(p))
        }

        InnerValue::Float(v) => {
            let p = *v.inner();
            let p = Decimal::try_from(p)?;

            // Ok this is an ugly hack. A bad bad hack.
            // It is slow and inefficient, BUT it works.
            // It is intended to fix floating point errors by leveraging the fact that
            // f64 strings somehow have the correct precision.

            // Todo: find a better way to do this
            let intended_precision = v
                .to_string()
                .split('.')
                .last()
                .map(|s| s.len())
                .unwrap_or(0);
            let p = p.round(intended_precision as i8);

            Ok(Fixed::from(p))
        }
        InnerValue::Currency(v) => {
            Ok(v.inner().value().clone())
        }
        InnerValue::Bool(v) => {
            if *v.inner() {
                Ok(Fixed::one())
            } else {
                Ok(Fixed::zero())
            }
        }
        InnerValue::String(_) => {
            Err(Error::ValueConversion {
                src_type: ValueType::String,
                dst_type: ValueType::Fixed,
            })
        }
        InnerValue::Array(v) => {
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
        InnerValue::Object(v) => {
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
map_type!(Range, Fixed);

overload_operator!(Fixed, arithmetic);
overload_operator!(Fixed, deref);

//
// Trait implementations
//

impl FromStr for Fixed {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.replace(',', "").parse::<FixedInner>()?.into())
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

    fn is_operator_supported(&self, _: &Self, _: ArithmeticOperation) -> bool {
        true
    }
}

impl BooleanOperationExt for Fixed {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => left != &Fixed::zero() && right != &Fixed::zero(),
            BooleanOperation::Or => left != &Fixed::zero() || right != &Fixed::zero(),

            BooleanOperation::LT => *left.inner() < *right.inner(),
            BooleanOperation::GT => *left.inner() > *right.inner(),
            BooleanOperation::LTE => *left.inner() <= *right.inner(),
            BooleanOperation::GTE => *left.inner() >= *right.inner(),
            BooleanOperation::EQ => *left.inner() == *right.inner(),
            BooleanOperation::NEQ => *left.inner() != *right.inner(),
            BooleanOperation::Not => left == &Fixed::zero(),
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
    use super::*;
    use crate::fixed;
    use fpdec::Decimal;

    #[test]
    fn test_arithmetic() {
        let fixed = Fixed::from_str("10.0").unwrap();
        assert!(fixed.is_operator_supported(&fixed, ArithmeticOperation::Add));
        assert!(fixed.is_operator_supported(&fixed, ArithmeticOperation::Subtract));
        assert!(fixed.is_operator_supported(&fixed, ArithmeticOperation::Multiply));
        assert!(fixed.is_operator_supported(&fixed, ArithmeticOperation::Divide));
        assert!(fixed.is_operator_supported(&fixed, ArithmeticOperation::Modulo));
        assert!(fixed.is_operator_supported(&fixed, ArithmeticOperation::Exponentiate));
        assert!(fixed.is_operator_supported(&fixed, ArithmeticOperation::Negate));

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

        assert_eq!(
            Fixed::arithmetic_neg(&Fixed::from_str("10").unwrap()).unwrap(),
            Fixed::from_str("-10").unwrap()
        );

        assert!(Currency::is_operator_supported(
            &Currency::from_str("$10.00").unwrap(),
            &Currency::from_str("$10.00").unwrap(),
            ArithmeticOperation::Add
        ));

        assert!(Currency::is_operator_supported(
            &Currency::from_str("$10.00").unwrap(),
            &Currency::from_str("$10.00").unwrap(),
            ArithmeticOperation::Subtract
        ));
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

        assert_eq!(
            Fixed::boolean_not(&Fixed::from_str("10").unwrap()).unwrap(),
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
            Value::fixed(Fixed::from_str("10.0").unwrap())
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

        assert_eq!(
            Fixed::try_from(Value::from(false)).unwrap(),
            Fixed::from_str("0").unwrap()
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
            Fixed::try_from(Value::try_from(vec![(Value::from("a"), Value::from(1))]).unwrap())
                .unwrap(),
            Fixed::from_str("1").unwrap()
        );

        // from multiple element array should fail
        assert!(Fixed::try_from(Value::from(vec![Value::from(1), Value::from(2)])).is_err());

        // from multiple element object should fail
        assert!(Fixed::try_from(
            Value::try_from(vec![
                (Value::from("a"), Value::from(1)),
                (Value::from("b"), Value::from(2))
            ])
            .unwrap()
        )
        .is_err());

        let value = Value::from(0..=99999999);
        assert!(Fixed::try_from(value).is_err());

        assert_eq!(
            Fixed::try_from(Value::from(U8::new(10))).unwrap(),
            fixed!(10)
        );

        assert_eq!(
            Fixed::try_from(Value::from(U16::new(10))).unwrap(),
            fixed!(10)
        );

        assert_eq!(
            Fixed::try_from(Value::from(U32::new(10))).unwrap(),
            fixed!(10)
        );

        assert_eq!(
            Fixed::try_from(Value::from(U64::new(10))).unwrap(),
            fixed!(10)
        );

        assert_eq!(
            Fixed::try_from(Value::from(I8::new(10))).unwrap(),
            fixed!(10)
        );

        assert_eq!(
            Fixed::try_from(Value::from(I16::new(10))).unwrap(),
            fixed!(10)
        );

        assert_eq!(
            Fixed::try_from(Value::from(I32::new(10))).unwrap(),
            fixed!(10)
        );

        assert_eq!(
            Fixed::try_from(Value::from(I64::new(10))).unwrap(),
            fixed!(10)
        );
    }

    #[test]
    fn test_parse() {
        assert_eq!(Fixed::from_str("10.0").unwrap(), fixed!(10.0));
        assert_eq!(Fixed::from_str("10").unwrap(), fixed!(10));
        assert_eq!(Fixed::from_str("-10").unwrap(), fixed!(-10));
    }
}
