//! Float type
//!
//! This type represents a floating point number. It is a wrapper around `f64`.
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

/// Inner type of `Float`
pub type FloatInner = f64;

/// Subtype of `Value` that represents a float
#[derive(PartialOrd, Clone, Serialize, Deserialize, Default, Debug)]
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
    handle_into = |v: Float| Value::Float(v),
    handle_from = |v: Value| match v {
        Value::Float(v) => Ok(v),
        Value::Fixed(v) => {
            let p = *v.inner();
            let p: f64 = p.into();
            Ok(Float::from(p))
        }
        Value::Currency(v) => {
            let p = *v.inner().value().inner();
            let p: f64 = p.into();
            Ok(Float::from(p))
        }
        Value::Int(v) => {
            let p = *v.inner() as f64;
            Ok(Float::from(p))
        }
        Value::Bool(v) => {
            let p = *v.inner() as i64 as f64;
            Ok(Float::from(p))
        }
        Value::String(_) => {
            Err(Error::ValueConversion {
                src_type: ValueType::String,
                dst_type: ValueType::Float,
            })
        }
        Value::Array(v) => {
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
        Value::Object(v) => {
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
);

map_type!(Array, Float);
map_type!(Bool, Float);
map_type!(Int, Float);
map_type!(Fixed, Float);
map_type!(Currency, Float);
map_type!(Str, Float);
map_type!(Object, Float);

//
// Trait implementations
//

impl FromStr for Float {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.replace(",", "").parse::<FloatInner>()?.into())
    }
}

impl PartialEq for Float {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == std::cmp::Ordering::Equal
    }
}

impl Eq for Float {}

impl Ord for Float {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.inner().is_nan() && other.inner().is_nan() {
            std::cmp::Ordering::Equal
        } else if self.inner().is_nan() {
            std::cmp::Ordering::Less
        } else if other.inner().is_nan() {
            std::cmp::Ordering::Greater
        } else {
            self.inner().partial_cmp(other.inner()).unwrap()
        }
    }
}

impl std::hash::Hash for Float {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner().to_bits().hash(state)
    }
}

impl ArithmeticOperationExt for Float {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = left.inner().clone();
        let right = right.inner().clone();

        let result = match operation {
            ArithmeticOperation::Add => left + right,
            ArithmeticOperation::Subtract => left - right,
            ArithmeticOperation::Multiply => left * right,
            ArithmeticOperation::Divide => left / right,
            ArithmeticOperation::Modulo => left % right,
            ArithmeticOperation::Exponentiate => left.powf(right),
            ArithmeticOperation::Negate => -left,
        };

        if result.is_infinite() || result.is_nan() {
            Err(Error::Overflow)
        } else {
            Ok(result.into())
        }
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Float::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }
}

impl BooleanOperationExt for Float {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => *left.inner() != 0.0 && *right.inner() != 0.0,
            BooleanOperation::Or => *left.inner() != 0.0 || *right.inner() != 0.0,

            BooleanOperation::LT => *left.inner() < *right.inner(),
            BooleanOperation::GT => *left.inner() > *right.inner(),
            BooleanOperation::LTE => *left.inner() <= *right.inner(),
            BooleanOperation::GTE => *left.inner() >= *right.inner(),
            BooleanOperation::EQ => *left.inner() == *right.inner(),
            BooleanOperation::NEQ => *left.inner() != *right.inner(),
            BooleanOperation::Not => *left.inner() == 0.0,
        };

        Ok(result.into())
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Float::boolean_op(self, &self.clone(), BooleanOperation::Not)
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
        let a = Float::from(1.0);
        let b = Float::from(2.0);

        assert_eq!(
            Float::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap(),
            Float::from(3.0)
        );
        assert_eq!(
            Float::arithmetic_op(&a, &b, ArithmeticOperation::Subtract).unwrap(),
            Float::from(-1.0)
        );
        assert_eq!(
            Float::arithmetic_op(&a, &b, ArithmeticOperation::Multiply).unwrap(),
            Float::from(2.0)
        );
        assert_eq!(
            Float::arithmetic_op(&a, &b, ArithmeticOperation::Divide).unwrap(),
            Float::from(0.5)
        );
        assert_eq!(
            Float::arithmetic_op(&a, &b, ArithmeticOperation::Modulo).unwrap(),
            Float::from(1.0)
        );
        assert_eq!(
            Float::arithmetic_op(&a, &b, ArithmeticOperation::Exponentiate).unwrap(),
            Float::from(1.0)
        );
        assert_eq!(
            Float::arithmetic_op(&a, &b, ArithmeticOperation::Negate).unwrap(),
            Float::from(-1.0)
        );
    }

    #[test]
    fn test_boolean_logic() {
        let a = Float::from(1.0);
        let b = Float::from(2.0);

        assert_eq!(
            Float::boolean_op(&a, &b, BooleanOperation::And).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Float::boolean_op(&a, &b, BooleanOperation::Or).unwrap(),
            Value::from(true)
        );

        assert_eq!(
            Float::boolean_op(&a, &b, BooleanOperation::LT).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Float::boolean_op(&a, &b, BooleanOperation::GT).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Float::boolean_op(&a, &b, BooleanOperation::LTE).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Float::boolean_op(&a, &b, BooleanOperation::GTE).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Float::boolean_op(&a, &b, BooleanOperation::EQ).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            Float::boolean_op(&a, &b, BooleanOperation::NEQ).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            Float::boolean_op(&a, &b, BooleanOperation::Not).unwrap(),
            Value::from(false)
        );
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
            Float::try_from(Value::from(Dec!(1.0))).unwrap(),
            Float::from(1.0)
        );
        assert_eq!(
            Float::try_from(Value::from(true)).unwrap(),
            Float::from(1.0)
        );
        Float::try_from(Value::from("")).expect_err("Should fail");
        assert_eq!(
            Float::try_from(Value::from(Currency::from_fixed(Fixed::from(Dec!(1.0))))).unwrap(),
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
