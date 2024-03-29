//! Fixed-point decimal type
//!
//! This type is a wrapper around [`fpdec::Decimal`](https://docs.rs/fpdec/0.5.0/fpdec/struct.Decimal.html).
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use std::str::FromStr;

use crate::{
    inner_types::fixed::BoxedDecimal, operations::*, types::*, Error, InnerValue, Value,
    ValueTrait, ValueType,
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
        //
        // First we handle the edge cases of exp <= 0
        match exp.cmp(&Fixed::zero()) {
            std::cmp::Ordering::Equal => return Some(Fixed::one()),
            std::cmp::Ordering::Less => {
                let exp = Dec!(-1) * *exp.inner().clone();
                let inverse = self.checked_pow(&exp.into())?;
                let result = Fixed::one() / inverse;
                return result.ok();
            }
            _ => {}
        }

        //
        // To calculate a**b, we can use the fact that a**b == e**(b * ln(a))
        let a = *self.inner().clone();
        let b = *exp.inner().clone();

        //
        // Approximate ln(a) using the taylor series for ln(x) = (x-1) - (x-1)**2/2 + (x-1)**3/3 - [...]
        let a_s1 = a.checked_sub(Dec!(1))?;
        let mut ln_a_mul = a_s1;
        let mut ln_a = a_s1;
        let mut multiplier = Dec!(-1);
        for i in 2..=500 {
            ln_a_mul = ln_a_mul.checked_mul(a_s1)?;
            let factor = ln_a_mul.checked_div(Decimal::from(i))?;
            let factor = factor.checked_mul(multiplier)?;

            ln_a = ln_a.checked_add(factor)?;
            multiplier = multiplier.checked_mul(Dec!(-1))?;
        }

        //
        // santity check - high precision checked_mul can fail, but if we check scale
        // we can avoid panics with unchecked multiplication
        let _ = b.trunc().checked_mul(ln_a.trunc())?;

        //
        // Now, Finally we approximate e**(b * ln(a)) using the taylor series for e**x = 1 + x + x**2/2! + [...]
        let b_ln_a = b * ln_a;
        let mut multiplier = b_ln_a;
        let mut e_b_ln_a = Dec!(1).checked_add(b_ln_a)?;
        let mut divisor = Dec!(1);
        // 34! overflows Decimal so we must stop at 33 rounds
        for i in 2..=33 {
            divisor = divisor.checked_mul(Decimal::from(i))?; // i!
            multiplier *= b_ln_a; // x**i
            let factor = multiplier.checked_div(divisor)?; // x**i / i!
            e_b_ln_a = e_b_ln_a.checked_add(factor)?;
        }

        //
        // Since this is an approximation, we round to the maximum precision of a and b
        let result = e_b_ln_a.round(a.n_frac_digits().max(b.n_frac_digits()) as i8);
        Some(Self::new(BoxedDecimal::from(result)))
    }
}

map_value!(
    from = Fixed,
    handle_into = (v) { Value::fixed(v) },
    handle_from = (v) {
        match v.inner() {
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
                // f64 strings calculate the correct precision.

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
                let len = v.inner().len();
                match v.inner().values().next() {
                    Some(v) if len == 1 => {
                        Fixed::try_from(v.clone())
                    }

                    _ => Err(Error::ValueConversion {
                        src_type: ValueType::Object,
                        dst_type: ValueType::Fixed,
                    }),
                }
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
        self,
        right: Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = self.into_inner();
        let right = right.into_inner();

        let result = match operation {
            ArithmeticOperation::Add => left.checked_add(right),
            ArithmeticOperation::Subtract => left.checked_sub(right),
            ArithmeticOperation::Multiply => left.checked_mul(right),
            ArithmeticOperation::Divide => left.checked_div(right),
            ArithmeticOperation::Modulo => left.checked_rem(right),
            ArithmeticOperation::Exponentiate => {
                // Convert to floats
                let left = Float::try_from(Value::from(left))?;
                let right = Float::try_from(Value::from(right))?;

                let result = left.arithmetic_op(right, operation)?;
                Some(Fixed::try_from(Value::from(result))?.into_inner())
            }
        }
        .ok_or(Error::Overflow)?;

        Ok(result.into())
    }

    fn arithmetic_neg(self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Ok(Fixed::try_from(Value::from(-self.into_inner()))?)
    }
}

impl BooleanOperationExt for Fixed {
    fn boolean_op(self, right: Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => self != Fixed::zero() && right != Fixed::zero(),
            BooleanOperation::Or => self != Fixed::zero() || right != Fixed::zero(),

            BooleanOperation::LT => *self.inner() < *right.inner(),
            BooleanOperation::GT => *self.inner() > *right.inner(),
            BooleanOperation::LTE => *self.inner() <= *right.inner(),
            BooleanOperation::GTE => *self.inner() >= *right.inner(),
            BooleanOperation::EQ | BooleanOperation::StrictEQ => *self.inner() == *right.inner(),
            BooleanOperation::NEQ | BooleanOperation::StrictNEQ => *self.inner() != *right.inner(),
        };

        Ok(result.into())
    }

    fn boolean_not(self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Ok((self == Fixed::zero()).into())
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
        assert_eq!(
            Fixed::arithmetic_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Add
            )
            .unwrap(),
            Fixed::from_str("15").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Subtract
            )
            .unwrap(),
            Fixed::from_str("5").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Multiply
            )
            .unwrap(),
            Fixed::from_str("50").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Divide
            )
            .unwrap(),
            Fixed::from_str("2").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Modulo
            )
            .unwrap(),
            Fixed::from_str("0").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                ArithmeticOperation::Exponentiate
            )
            .unwrap(),
            Fixed::from_str("100000").unwrap()
        );

        assert_eq!(
            Fixed::arithmetic_neg(Fixed::from_str("10").unwrap()).unwrap(),
            Fixed::from_str("-10").unwrap()
        );
    }

    #[test]
    fn test_boolean_logic() {
        assert_eq!(
            Fixed::boolean_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                BooleanOperation::And
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                BooleanOperation::Or
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                BooleanOperation::LT
            )
            .unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Fixed::boolean_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                BooleanOperation::GT
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                BooleanOperation::LTE
            )
            .unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Fixed::boolean_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                BooleanOperation::GTE
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                BooleanOperation::EQ
            )
            .unwrap(),
            Value::from(false)
        );

        assert_eq!(
            Fixed::boolean_op(
                Fixed::from_str("10").unwrap(),
                Fixed::from_str("5").unwrap(),
                BooleanOperation::NEQ
            )
            .unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Fixed::boolean_not(Fixed::from_str("10").unwrap()).unwrap(),
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

    #[test]
    fn test_checked_pow() {
        assert_eq!(
            Fixed::from_str("2")
                .unwrap()
                .checked_pow(&Fixed::from_str("3").unwrap())
                .unwrap(),
            fixed!(8)
        );

        assert_eq!(
            Fixed::from_str("2")
                .unwrap()
                .checked_pow(&Fixed::from_str("0.5").unwrap())
                .unwrap(),
            fixed!(1.4)
        );

        assert_eq!(
            Fixed::from_str("2")
                .unwrap()
                .checked_pow(&Fixed::from_str("0").unwrap())
                .unwrap(),
            fixed!(1)
        );

        assert_eq!(
            Fixed::from_str("2")
                .unwrap()
                .checked_pow(&Fixed::from_str("-1").unwrap())
                .unwrap(),
            fixed!(0.5)
        );

        assert_eq!(
            Fixed::from_str("2")
                .unwrap()
                .checked_pow(&Fixed::from_str("-2").unwrap())
                .unwrap(),
            fixed!(0.25)
        );

        assert_eq!(
            Fixed::from_str("2")
                .unwrap()
                .checked_pow(&Fixed::from_str("-3").unwrap())
                .unwrap(),
            fixed!(0.125)
        );
    }
}
