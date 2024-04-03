//! Currency type
//!
//! This is a wrapper around `Fixed` that adds a currency symbol
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<symbol><value>`
//!
use crate::{operations::*, types::*, Error, InnerValue, Value, ValueTrait};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

pub use crate::inner_types::currency::CurrencyInner;

/// Subtype of `Value` that represents a currency
/// This is a wrapper around `Fixed` that adds a currency symbol
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Currency(CurrencyInner);
impl_value!(Currency, CurrencyInner, |v: &Self| v.inner().to_string());

impl Currency {
    /// Create a new `Currency` from a `Fixed`
    pub fn from_fixed(value: Fixed) -> Self {
        Self::from(CurrencyInner::from_fixed(value))
    }

    /// Resolve the precision of this `Currency` with another `Currency`
    pub fn resolve(self, other: Self) -> (Self, Self) {
        let (left, right) = self.into_inner().resolve(other.into_inner());
        (Self(left), Self(right))
    }
}

impl From<fpdec::Decimal> for Currency {
    fn from(value: fpdec::Decimal) -> Self {
        Currency::from_fixed(Fixed::from(value))
    }
}

map_value!(
    from = Currency,
    handle_into = (v) { Value::currency(v) },
    handle_from = (v) {
        match v.inner() {
            InnerValue::Currency(v) => Ok(v.clone()),
            _ => {
                let value = Fixed::try_from(v)?;
                let value = CurrencyInner::from_fixed(value);
                Ok(Currency(value))
            }
        }
    }
);

map_type!(Array, Currency);
map_type!(Object, Currency);
map_type!(Int, Currency);
map_type!(Float, Currency);
map_type!(Fixed, Currency);
map_type!(Bool, Currency);
map_type!(Str, Currency);
map_type!(Range, Currency);

overload_operator!(Currency, arithmetic);
overload_operator!(Currency, deref);

impl Currency {
    /// Get the symbol of this `Currency`
    pub fn symbol(&self) -> &Option<String> {
        self.inner().symbol()
    }

    /// Get the precision of this `Currency`
    pub fn precision(&self) -> i8 {
        self.inner().precision()
    }

    /// Get the value of this `Currency`
    pub fn value(&self) -> &Fixed {
        self.inner().value()
    }
}

impl FromStr for Currency {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let value = CurrencyInner::from_str(s)?;
        Ok(Currency::from(value))
    }
}

impl ArithmeticOperationExt for Currency {
    fn arithmetic_op(self, right: Self, operation: ArithmeticOperation) -> Result<Self, Error> {
        let (left, right) = (self.into_inner(), right.into_inner());
        left.arithmetic_op(right, operation).map(Self::from)
    }

    fn arithmetic_neg(self) -> Result<Self, Error>
    where
        Self: Sized,
    {
        self.into_inner().arithmetic_neg().map(Self::from)
    }
}

impl BooleanOperationExt for Currency {
    fn boolean_op(self, right: Self, operation: BooleanOperation) -> Result<Value, Error> {
        self.into_inner()
            .into_value()
            .boolean_op(right.into_inner().into_value(), operation)
    }

    fn boolean_not(self) -> Result<Value, Error>
    where
        Self: Sized,
    {
        self.into_inner().into_value().boolean_not()
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
        let a = Currency::from_str("10.00$").unwrap();
        let b = Currency::from_str("5.00$").unwrap();

        let result =
            Currency::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Add).unwrap();
        assert_eq!(result.to_string(), "15.00$".to_string());

        let result =
            Currency::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Subtract).unwrap();
        assert_eq!(result.to_string(), "5.00$".to_string());

        let result =
            Currency::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Multiply).unwrap();
        assert_eq!(result.to_string(), "50.00$".to_string());

        let result =
            Currency::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Divide).unwrap();
        assert_eq!(result.to_string(), "2.00$".to_string());

        let result =
            Currency::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Exponentiate)
                .unwrap();
        assert_eq!(result.to_string(), "100000.00$".to_string());

        // Different symbols and precisions
        let a = Currency::from_str("10.00$").unwrap();
        let b = Currency::from_str("5¥").unwrap();
        let result =
            Currency::arithmetic_op(a.clone(), b.clone(), ArithmeticOperation::Add).unwrap();
        assert_eq!(result.to_string(), "15.00".to_string());

        let result = Currency::arithmetic_neg(Currency::from_str("10.00$").unwrap()).unwrap();
        assert_eq!(result.to_string(), "-10.00$".to_string());
    }

    #[test]
    fn test_boolean_logic() {
        let result = Currency::boolean_op(
            Currency::from_str("0.00").unwrap(),
            Currency::from_str("0.00").unwrap(),
            BooleanOperation::And,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result = Currency::boolean_op(
            Currency::from_str("0.00").unwrap(),
            Currency::from_str("1.00").unwrap(),
            BooleanOperation::Or,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            Currency::from_str("1.00").unwrap(),
            Currency::from_str("0.00").unwrap(),
            BooleanOperation::LT,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result = Currency::boolean_op(
            Currency::from_str("1.00").unwrap(),
            Currency::from_str("0.00").unwrap(),
            BooleanOperation::GT,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            Currency::from_str("0.00").unwrap(),
            Currency::from_str("0.00").unwrap(),
            BooleanOperation::LTE,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            Currency::from_str("0.00").unwrap(),
            Currency::from_str("0.00").unwrap(),
            BooleanOperation::GTE,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            Currency::from_str("0.00").unwrap(),
            Currency::from_str("0.00").unwrap(),
            BooleanOperation::EQ,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            Currency::from_str("0.00").unwrap(),
            Currency::from_str("0.00").unwrap(),
            BooleanOperation::NEQ,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result = Currency::boolean_not(Currency::from_str("10.00").unwrap()).unwrap();
        assert_eq!(result, Bool::from(false).into());
    }

    #[test]
    fn test_to_string() {
        let value = Currency::from_str("10.00").unwrap();
        assert_eq!(value.to_string(), "10.00".to_string());

        let value = Currency::from_str("10").unwrap();
        assert_eq!(value.to_string(), "10".to_string());

        let value = Currency::from_str("¥10").unwrap();
        assert_eq!(value.to_string(), "10¥".to_string());

        let value = Currency::new(CurrencyInner::new(None, 5, fixed!(10.123456789)));
        assert_eq!(value.to_string(), "10.12346".to_string());
    }

    #[test]
    fn test_from() {
        assert_eq!(
            Currency::try_from(Value::from(10)).unwrap(),
            Currency::from_fixed(fixed!(10))
        );
        assert_eq!(
            Currency::try_from(Value::from(10.0)).unwrap(),
            Currency::from_fixed(fixed!(10))
        );
        assert_eq!(
            Currency::try_from(Value::from(fixed!(10.0))).unwrap(),
            Currency::from_fixed(fixed!(10.0))
        );
        assert_eq!(
            Currency::try_from(Value::from(true)).unwrap(),
            Currency::from_fixed(fixed!(1))
        );

        // string should fail
        assert!(Currency::try_from(Value::from("")).is_err());

        // array with 1 element
        let value = Value::from(vec![Value::from(10)]);
        assert_eq!(
            Currency::try_from(value).unwrap(),
            Currency::from_fixed(fixed!(10))
        );

        // array with 2 elements should fail
        let value = Value::from(vec![10, 10]);
        assert!(Currency::try_from(value).is_err());

        // object with 1 element
        let value = Value::try_from(vec![("a", 10)]).unwrap();
        assert_eq!(
            Currency::try_from(value).unwrap(),
            Currency::from_fixed(fixed!(10))
        );

        // object with 2 elements should fail
        let value = Value::try_from(vec![("a", 10), ("b", 10)]).unwrap();
        assert!(Currency::try_from(value).is_err());
    }

    #[test]
    fn test_parse() {
        let value = Currency::from_str("10.00$").unwrap();
        assert_eq!(value.symbol(), &Some("$".to_string()));
        assert_eq!(value.precision(), 2);
        assert_eq!(*value.value(), fixed!(10.00));

        let value = Currency::from_str("10").unwrap();
        assert_eq!(value.symbol(), &None);
        assert_eq!(value.precision(), 0);
        assert_eq!(*value.value(), fixed!(10));

        let value = Currency::from_str("¥10").unwrap();
        assert_eq!(value.symbol(), &Some("¥".to_string()));
        assert_eq!(value.precision(), 0);
        assert_eq!(*value.value(), fixed!(10));
    }
}
