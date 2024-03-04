//! Float type
//!
//! This type represents a floating point number. It is a wrapper around `f64`.
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use crate::{operations::*, types::*, Error, InnerValue, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

/// Inner type of `Float`
pub type FloatInner = f64;

/// Subtype of `Value` that represents a float
#[derive(Clone, Serialize, Deserialize, Default)]
pub struct Float(FloatInner);
impl_value!(Float, FloatInner, |v: &Self| {
    let mut v = *v.inner();
    if v == -0.0 {
        v = 0.0;
    }

    let mut f = format!("{:}", v);
    if !f.contains('.') {
        f += ".0";
    }

    f
});

map_value!(
    from = Float,
    handle_into = (v) { Value::float(v) },
    handle_from = (v) {
        match v.inner() {
            InnerValue::Range(_) => Self::try_from(v.as_a::<Array>()?),
            InnerValue::Float(v) => Ok(v.clone()),
            InnerValue::Fixed(v) => {
                let p = v.inner().clone();
                let p: f64 = p.into();
                Ok(Float::from(p))
            }
            InnerValue::Currency(v) => {
                let p = v.inner().value().inner().clone();
                let p: f64 = p.into();
                Ok(Float::from(p))
            }

            InnerValue::U8(v) => {
                let p = *v.inner() as f64;
                Ok(Float::from(p))
            }

            InnerValue::U16(v) => {
                let p = *v.inner() as f64;
                Ok(Float::from(p))
            }

            InnerValue::U32(v) => {
                let p = *v.inner() as f64;
                Ok(Float::from(p))
            }

            InnerValue::U64(v) => {
                let p = *v.inner() as f64;
                Ok(Float::from(p))
            }

            InnerValue::I8(v) => {
                let p = *v.inner() as f64;
                Ok(Float::from(p))
            }

            InnerValue::I16(v) => {
                let p = *v.inner() as f64;
                Ok(Float::from(p))
            }

            InnerValue::I32(v) => {
                let p = *v.inner() as f64;
                Ok(Float::from(p))
            }

            InnerValue::I64(v) => {
                let p = *v.inner() as f64;
                Ok(Float::from(p))
            }

            InnerValue::Bool(v) => {
                let p = *v.inner() as i64 as f64;
                Ok(Float::from(p))
            }
            InnerValue::String(_) => {
                Err(Error::ValueConversion {
                    src_type: ValueType::String,
                    dst_type: ValueType::Float,
                })
            }
            InnerValue::Array(v) => {
                if v.inner().len() == 1 {
                    let v = v.inner()[0].clone();
                    Float::try_from(v)
                } else {
                    Err(Error::ValueConversion {
                        src_type: ValueType::Array,
                        dst_type: ValueType::Float,
                    })
                }
            }
            InnerValue::Object(v) => {
                if v.inner().len() == 1 {
                    let v = v.inner().values().next().unwrap().clone();
                    Float::try_from(v)
                } else {
                    Err(Error::ValueConversion {
                        src_type: ValueType::Object,
                        dst_type: ValueType::Float,
                    })
                }
            }
        }
    }
);

map_type!(Array, Float);
map_type!(Bool, Float);
map_type!(Int, Float);
map_type!(Fixed, Float);
map_type!(Currency, Float);
map_type!(Str, Float);
map_type!(Object, Float);
map_type!(Range, Float);

overload_operator!(Float, arithmetic);
overload_operator!(Float, deref);

//
// Trait implementations
//

impl FromStr for Float {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.replace(',', "").parse::<FloatInner>()?.into())
    }
}

impl PartialEq for Float {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == std::cmp::Ordering::Equal
    }
}

impl Eq for Float {}

impl PartialOrd for Float {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.inner().total_cmp(other.inner()))
    }
}

impl Ord for Float {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl std::hash::Hash for Float {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner().to_bits().hash(state)
    }
}

impl ArithmeticOperationExt for Float {
    fn arithmetic_op(
        self,
        right: Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = self.into_inner();
        let right = right.into_inner();

        let result = match operation {
            ArithmeticOperation::Add => left + right,
            ArithmeticOperation::Subtract => left - right,
            ArithmeticOperation::Multiply => left * right,
            ArithmeticOperation::Divide => left / right,
            ArithmeticOperation::Modulo => left % right,
            ArithmeticOperation::Exponentiate => left.powf(right),
        };

        if result.is_infinite() || result.is_nan() {
            Err(Error::Overflow)
        } else {
            Ok(result.into())
        }
    }

    fn arithmetic_neg(self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Ok(Self(-(self.into_inner())))
    }
}

impl BooleanOperationExt for Float {
    fn boolean_op(self, right: Self, operation: BooleanOperation) -> Result<Value, Error> {
        let left = self.into_inner();
        let right = right.into_inner();

        let result = match operation {
            BooleanOperation::And => left != 0.0 && right != 0.0,
            BooleanOperation::Or => left != 0.0 || right != 0.0,

            BooleanOperation::LT => left < right,
            BooleanOperation::GT => left > right,
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
        Ok((self.into_inner() == 0.0).into())
    }
}

//
// Tests
//

#[cfg(test)]
mod test {
    use super::*;
    use crate::fixed;
    use fpdec::Decimal;

    #[test]
    fn test_arithmetic() {
        let a = Float::from(1.0);
        let b = Float::from(2.0);

        assert_eq!(
            Float::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Add).unwrap(),
            Float::from(3.0)
        );
        assert_eq!(
            Float::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Subtract).unwrap(),
            Float::from(-1.0)
        );
        assert_eq!(
            Float::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Multiply).unwrap(),
            Float::from(2.0)
        );
        assert_eq!(
            Float::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Divide).unwrap(),
            Float::from(0.5)
        );
        assert_eq!(
            Float::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Modulo).unwrap(),
            Float::from(1.0)
        );
        assert_eq!(
            Float::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Exponentiate).unwrap(),
            Float::from(1.0)
        );
        assert_eq!(Float::arithmetic_neg(a.clone()).unwrap(), Float::from(-1.0));

        assert!(Float::arithmetic_op(
            Float::from(-1.0),
            Float::from(0.0),
            ArithmeticOperation::Divide
        )
        .is_err());
    }

    #[test]
    fn test_boolean_logic() {
        let a = Float::from(1.0);
        let b = Float::from(2.0);

        assert_eq!(
            Float::boolean_op(a.clone(), b.clone(), BooleanOperation::And).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Float::boolean_op(a.clone(), b.clone(), BooleanOperation::Or).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Float::boolean_op(a.clone(), b.clone(), BooleanOperation::LT).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Float::boolean_op(a.clone(), b.clone(), BooleanOperation::GT).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Float::boolean_op(a.clone(), b.clone(), BooleanOperation::LTE).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Float::boolean_op(a.clone(), b.clone(), BooleanOperation::GTE).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Float::boolean_op(a.clone(), b.clone(), BooleanOperation::EQ).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Float::boolean_op(a.clone(), b.clone(), BooleanOperation::NEQ).unwrap(),
            Value::from(true)
        );
        assert_eq!(Float::boolean_not(a.clone()).unwrap(), Value::from(false));
    }

    #[test]
    fn test_to_string() {
        let a = Float::from(1.0);
        assert_eq!(a.to_string(), "1.0");

        let a = Float::from(1.22);
        assert_eq!(a.to_string(), "1.22");

        let a = Float::from(-0.0);
        assert_eq!(a.to_string(), "0.0");
    }

    #[test]
    fn test_from() {
        assert_eq!(Float::try_from(Value::from(1.0)).unwrap(), Float::from(1.0));
        assert_eq!(Float::try_from(Value::from(1)).unwrap(), Float::from(1.0));
        assert_eq!(
            Float::try_from(Value::from(fixed!(1.0))).unwrap(),
            Float::from(1.0)
        );
        assert_eq!(
            Float::try_from(Value::from(true)).unwrap(),
            Float::from(1.0)
        );
        Float::try_from(Value::from("")).expect_err("Should fail");
        assert_eq!(
            Float::try_from(Value::from(Currency::from_fixed(fixed!(1.0)))).unwrap(),
            Float::from(1.0)
        );

        // Array with 1 element
        assert_eq!(
            Float::try_from(Value::from(vec![Value::from(1.0)])).unwrap(),
            Float::from(1.0)
        );

        // Object with 1 element
        assert_eq!(
            Float::try_from(Value::try_from(vec![(Value::from(1), Value::from(1.0))]).unwrap())
                .unwrap(),
            Float::from(1.0)
        );

        // Array with more than 1 element should fail
        Float::try_from(Value::from(vec![Value::from(1.0), Value::from(2.0)]))
            .expect_err("Should fail");

        // Object with more than 1 element should fail
        Float::try_from(
            Value::try_from(vec![
                (Value::from(1), Value::from(1.0)),
                (Value::from(2), Value::from(2.0)),
            ])
            .unwrap(),
        )
        .expect_err("Should fail");

        let value = Value::from(0..=99999999);
        assert!(Float::try_from(value).is_err());

        assert_eq!(
            Float::try_from(Value::from(U8::new(10))).unwrap(),
            Float::from(10.0)
        );

        assert_eq!(
            Float::try_from(Value::from(U16::new(10))).unwrap(),
            Float::from(10.0)
        );

        assert_eq!(
            Float::try_from(Value::from(U32::new(10))).unwrap(),
            Float::from(10.0)
        );

        assert_eq!(
            Float::try_from(Value::from(U64::new(10))).unwrap(),
            Float::from(10.0)
        );

        assert_eq!(
            Float::try_from(Value::from(I8::new(10))).unwrap(),
            Float::from(10.0)
        );

        assert_eq!(
            Float::try_from(Value::from(I16::new(10))).unwrap(),
            Float::from(10.0)
        );

        assert_eq!(
            Float::try_from(Value::from(I32::new(10))).unwrap(),
            Float::from(10.0)
        );

        assert_eq!(
            Float::try_from(Value::from(I64::new(10))).unwrap(),
            Float::from(10.0)
        );
    }

    #[test]
    fn test_parse() {
        assert_eq!("1.0".parse::<Float>().unwrap(), Float::from(1.0));
        assert_eq!("1".parse::<Float>().unwrap(), Float::from(1.0));
        assert_eq!("1.22".parse::<Float>().unwrap(), Float::from(1.22));
        assert_eq!("-1.22".parse::<Float>().unwrap(), Float::from(-1.22));
        assert_eq!("0.0".parse::<Float>().unwrap(), Float::from(0.0));
        assert_eq!("-0.0".parse::<Float>().unwrap(), Float::from(-0.0));
        assert!("".parse::<Float>().is_err());
        assert!("a".parse::<Float>().is_err());
    }
}
