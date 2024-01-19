//! Int type
//!
//! This type represents an integer. It is a wrapper around `i64`
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use std::str::FromStr;

use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};

/// Inner type of `Int`
pub type IntInner = i64;

/// Subtype of `Value` that represents an integer
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug)]
pub struct Int(IntInner);
impl_value!(Int, IntInner, |v: &Self| v.inner().to_string());

impl Int {
    /// Creates a new Int from a string representation of a base-n number
    /// The string must be in the form of `0b<binary>`, `0o<octal>`, `0x<hex>`, or `0<octal>`
    ///
    /// # Examples
    /// ```rust
    /// use polyvalue::types::Int;
    ///
    /// let a = Int::from_str_radix("0b1010").unwrap();
    /// assert_eq!(a, Int::from(10));
    ///
    /// let a = Int::from_str_radix("0o12").unwrap();
    /// assert_eq!(a, Int::from(10));
    ///
    /// let a = Int::from_str_radix("012").unwrap();
    /// assert_eq!(a, Int::from(10));
    /// ```
    pub fn from_str_radix(s: &str) -> Result<Self, Error> {
        if s.len() < 2 {
            return Err(Error::ValueConversion {
                src_type: ValueType::String,
                dst_type: ValueType::Int,
            });
        }

        let mut s = s.trim().to_lowercase();
        if s.remove(0) != '0' {
            return Err(Error::ValueConversion {
                src_type: ValueType::String,
                dst_type: ValueType::Int,
            });
        }

        let prefix = s.remove(0);
        let radix = match prefix {
            'b' => 2,
            'o' => 8,
            '0'..='7' => {
                s.insert(0, prefix);
                8
            }
            'x' => 16,
            _ => {
                return Err(Error::ValueConversion {
                    src_type: ValueType::String,
                    dst_type: ValueType::Int,
                })
            }
        };

        let value = IntInner::from_str_radix(&s, radix).map_err(|_| Error::ValueConversion {
            src_type: ValueType::String,
            dst_type: ValueType::Int,
        })?;

        Ok(Int::from(value))
    }
}

map_value!(
    from = Int,
    handle_into = Value::Int,
    handle_from = |v: Value| match v {
        Value::Range(_) => Self::try_from(v.as_a::<Array>()?),
        Value::Int(v) => Ok(v),

        Value::U8(v) => Ok(Int::new(*v.inner() as IntInner)),
        Value::U16(v) => Ok(Int::new(*v.inner() as IntInner)),
        Value::U32(v) => Ok(Int::new(*v.inner() as IntInner)),
        Value::U64(v) => Ok(Int::new(*v.inner() as IntInner)),
        Value::I8(v) => Ok(Int::new(*v.inner() as IntInner)),
        Value::I16(v) => Ok(Int::new(*v.inner() as IntInner)),
        Value::I32(v) => Ok(Int::new(*v.inner() as IntInner)),
        Value::I64(v) => Ok(Int::new(*v.inner() as IntInner)),

        Value::Fixed(v) => {
            let p = *v.inner();
            let p: IntInner = p.trunc().coefficient() as IntInner;
            Ok(Int::from(p))
        }
        Value::Float(v) => {
            let p = *v.inner();
            let p = p as i64;
            Ok(Int::from(p))
        }
        Value::Currency(v) => {
            let p = *v.inner().value().inner();
            let p: IntInner = p.trunc().coefficient() as IntInner;
            Ok(Int::from(p))
        }
        Value::Bool(v) => {
            let p = *v.inner() as i64;
            Ok(Int::from(p))
        }
        Value::String(_) => {
            Err(Error::ValueConversion {
                src_type: ValueType::String,
                dst_type: ValueType::Int,
            })
        }
        Value::Array(v) => {
            if v.inner().len() == 1 {
                let v = v.inner()[0].clone();
                Int::try_from(v)
            } else {
                Err(Error::ValueConversion {
                    src_type: ValueType::Array,
                    dst_type: ValueType::Int,
                })
            }
        }
        Value::Object(v) => {
            if v.inner().len() == 1 {
                let v = v.inner().values().next().unwrap().clone();
                Int::try_from(v)
            } else {
                Err(Error::ValueConversion {
                    src_type: ValueType::Object,
                    dst_type: ValueType::Int,
                })
            }
        }
    }
);

impl From<usize> for Value {
    fn from(v: usize) -> Self {
        Int::from(v).into()
    }
}

impl From<usize> for Int {
    fn from(v: usize) -> Self {
        Int(v as IntInner)
    }
}

impl From<i32> for Value {
    fn from(v: i32) -> Self {
        Int::from(v).into()
    }
}

impl From<i32> for Int {
    fn from(v: i32) -> Self {
        Int(v as IntInner)
    }
}

impl FromStr for Int {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.replace(',', "").parse::<IntInner>()?.into())
    }
}

map_type!(Array, Int);
map_type!(Bool, Int);
map_type!(Fixed, Int);
map_type!(Float, Int);
map_type!(Currency, Int);
map_type!(Str, Int);
map_type!(Object, Int);
map_type!(Range, Int);

impl ArithmeticOperationExt for Int {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = *left.inner();
        let right = *right.inner();

        let result = match operation {
            ArithmeticOperation::Add => left.checked_add(right),
            ArithmeticOperation::Subtract => left.checked_sub(right),
            ArithmeticOperation::Multiply => left.checked_mul(right),
            ArithmeticOperation::Divide => left.checked_div(right),
            ArithmeticOperation::Modulo => left.checked_rem(right),
            ArithmeticOperation::Exponentiate => {
                if let Ok(right) = right.try_into() {
                    left.checked_pow(right)
                } else {
                    None
                }
            }
            ArithmeticOperation::Negate => Some(-left),
        }
        .ok_or(Error::Overflow)?;
        Ok(result.into())
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Int::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }
}

impl BooleanOperationExt for Int {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => *left.inner() != 0 && *right.inner() != 0,
            BooleanOperation::Or => *left.inner() != 0 || *right.inner() != 0,

            BooleanOperation::LT => *left.inner() < *right.inner(),
            BooleanOperation::GT => *left.inner() > *right.inner(),
            BooleanOperation::LTE => *left.inner() <= *right.inner(),
            BooleanOperation::GTE => *left.inner() >= *right.inner(),
            BooleanOperation::EQ => *left.inner() == *right.inner(),
            BooleanOperation::NEQ => *left.inner() != *right.inner(),
            BooleanOperation::Not => *left.inner() == 0,
        };

        Ok(result.into())
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Int::boolean_op(self, &self.clone(), BooleanOperation::Not)
    }
}

//
// Tests
//

#[cfg(test)]
mod test {
    use fpdec::{Dec, Decimal};

    use super::*;

    #[test]
    fn test_arithmetic() {
        let a = Int::from(10);
        let b = Int::from(5);

        assert_eq!(
            Int::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap(),
            Int::from(15)
        );
        assert_eq!(
            Int::arithmetic_op(&a, &b, ArithmeticOperation::Subtract).unwrap(),
            Int::from(5)
        );
        assert_eq!(
            Int::arithmetic_op(&a, &b, ArithmeticOperation::Multiply).unwrap(),
            Int::from(50)
        );
        assert_eq!(
            Int::arithmetic_op(&a, &b, ArithmeticOperation::Divide).unwrap(),
            Int::from(2)
        );
        assert_eq!(
            Int::arithmetic_op(&a, &b, ArithmeticOperation::Modulo).unwrap(),
            Int::from(0)
        );
        assert_eq!(
            Int::arithmetic_op(&a, &b, ArithmeticOperation::Exponentiate).unwrap(),
            Int::from(100000)
        );
        assert_eq!(
            Int::arithmetic_op(&a, &b, ArithmeticOperation::Negate).unwrap(),
            Int::from(-10)
        );
    }

    #[test]
    fn test_boolean_logic() {
        let a = Int::from(10);
        let b = Int::from(5);

        assert_eq!(
            Int::boolean_op(&a, &b, BooleanOperation::And).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Int::boolean_op(&a, &b, BooleanOperation::Or).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Int::boolean_op(&a, &b, BooleanOperation::LT).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Int::boolean_op(&a, &b, BooleanOperation::GT).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Int::boolean_op(&a, &b, BooleanOperation::LTE).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Int::boolean_op(&a, &b, BooleanOperation::GTE).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Int::boolean_op(&a, &b, BooleanOperation::EQ).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Int::boolean_op(&a, &b, BooleanOperation::NEQ).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Int::boolean_op(&a, &b, BooleanOperation::Not).unwrap(),
            Value::from(false)
        );
    }

    #[test]
    fn test_to_string() {
        let a = Int::from(10);
        assert_eq!(a.to_string(), "10");
    }

    #[test]
    fn test_from() {
        let a = Int::from(10);

        assert_eq!(Value::from(a.clone()), Value::Int(a.clone()));

        assert_eq!(Int::try_from(Value::from(1.0)).unwrap(), Int::from(1));
        assert_eq!(Int::try_from(Value::from(1)).unwrap(), Int::from(1));
        assert_eq!(Int::try_from(Value::from(true)).unwrap(), Int::from(1));
        assert_eq!(Int::try_from(Value::from(Dec!(1.0))).unwrap(), Int::from(1));
        assert_eq!(
            Int::try_from(Value::from(Currency::from_fixed(Fixed::from(Dec!(1.0))))).unwrap(),
            Int::from(1)
        );
        Int::try_from(Value::from("")).expect_err("Should fail");

        // Try from array with one float
        let a = Array::from(vec![Value::from(1.0)]);
        assert_eq!(Int::try_from(Value::from(a)).unwrap(), Int::from(1));

        // Try from array with multiple floats ( should fail )
        let a = Array::from(vec![Value::from(1.0), Value::from(2.0)]);
        Int::try_from(Value::from(a)).expect_err("Should fail");

        // Try from object with one float
        let mut o = Object::try_from(vec![("a".into(), Value::from(1.0))]).unwrap();
        assert_eq!(Int::try_from(Value::from(o)).unwrap(), Int::from(1));

        // Try from object with multiple floats ( should fail )
        o = Object::try_from(vec![
            ("a".into(), Value::from(1.0)),
            ("b".into(), Value::from(2.0)),
        ])
        .unwrap();
        Int::try_from(Value::from(o)).expect_err("Should fail");
    }

    #[test]
    fn test_parse() {
        assert_eq!(Int::from_str("10").unwrap(), Int::from(10));

        assert_eq!(Int::from_str_radix("0b1010").unwrap(), Int::from(10));
        assert_eq!(Int::from_str_radix("0o12").unwrap(), Int::from(10));
        assert_eq!(Int::from_str_radix("012").unwrap(), Int::from(10));
        assert_eq!(Int::from_str_radix("0xFAF").unwrap(), Int::from(4015));
    }
}
