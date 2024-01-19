//! Currency type
//!
//! This is a wrapper around `Fixed` that adds a currency symbol
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<symbol><value>`
//!
use crate::{operations::*, types::*, Error, Value, ValueTrait};
use serde::{Deserialize, Serialize};
use std::str::FromStr;

pub use crate::inner_currency::CurrencyInner;

/// Subtype of `Value` that represents a currency
/// This is a wrapper around `Fixed` that adds a currency symbol
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug)]
pub struct Currency(CurrencyInner);
impl_value!(Currency, CurrencyInner, |v: &Self| v.inner().to_string());

impl Currency {
    /// Create a new `Currency` from a `Fixed`
    pub fn from_fixed(value: Fixed) -> Self {
        Self::from(CurrencyInner::from_fixed(value))
    }

    /// Resolve the precision of this `Currency` with another `Currency`
    pub fn resolve(&self, other: &Self) -> (Self, Self) {
        let (left, right) = self.inner().resolve(other.inner());
        (Self(left), Self(right))
    }
}

map_value!(
    from = Currency,
    handle_into = Value::Currency,
    handle_from = |v: Value| {
        match v {
            Value::Currency(v) => Ok(v),
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
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, Error> {
        let (left, right) = left.inner().resolve(right.inner());
        let resulting_value = Fixed::arithmetic_op(left.value(), right.value(), operation)?;
        let result = CurrencyInner::new(left.symbol().clone(), left.precision(), resulting_value);
        Ok(Currency::from(result))
    }

    fn arithmetic_neg(&self) -> Result<Self, Error>
    where
        Self: Sized,
    {
        Currency::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }

    fn is_operator_supported(&self, _: &Self, _: ArithmeticOperation) -> bool {
        true
    }
}

impl BooleanOperationExt for Currency {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        Fixed::boolean_op(left.inner().value(), right.inner().value(), operation)
    }

    fn boolean_not(&self) -> Result<Value, Error>
    where
        Self: Sized,
    {
        Currency::boolean_op(self, &self.clone(), BooleanOperation::Not)
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
        let a = Currency::from_str("$10.00").unwrap();
        let b = Currency::from_str("$5.00").unwrap();

        let result = Currency::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap();
        assert_eq!(result.to_string(), "$15.00".to_string());

        let result = Currency::arithmetic_op(&a, &b, ArithmeticOperation::Subtract).unwrap();
        assert_eq!(result.to_string(), "$5.00".to_string());

        let result = Currency::arithmetic_op(&a, &b, ArithmeticOperation::Multiply).unwrap();
        assert_eq!(result.to_string(), "$50.00".to_string());

        let result = Currency::arithmetic_op(&a, &b, ArithmeticOperation::Divide).unwrap();
        assert_eq!(result.to_string(), "$2.00".to_string());

        let result = Currency::arithmetic_op(&a, &b, ArithmeticOperation::Exponentiate).unwrap();
        assert_eq!(result.to_string(), "$100000.00".to_string());

        let result = Currency::arithmetic_op(&a, &b, ArithmeticOperation::Negate).unwrap();
        assert_eq!(result.to_string(), "$-10.00".to_string());

        // Different symbols and precisions
        let a = Currency::from_str("$10.00").unwrap();
        let b = Currency::from_str("¥5").unwrap();
        let result = Currency::arithmetic_op(&a, &b, ArithmeticOperation::Add).unwrap();
        assert_eq!(result.to_string(), "15.00".to_string());
    }

    #[test]
    fn test_boolean_logic() {
        let result = Currency::boolean_op(
            &Currency::from_str("$0.00").unwrap(),
            &Currency::from_str("$0.00").unwrap(),
            BooleanOperation::And,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result = Currency::boolean_op(
            &Currency::from_str("$0.00").unwrap(),
            &Currency::from_str("$1.00").unwrap(),
            BooleanOperation::Or,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            &Currency::from_str("$1.00").unwrap(),
            &Currency::from_str("$0.00").unwrap(),
            BooleanOperation::LT,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result = Currency::boolean_op(
            &Currency::from_str("$1.00").unwrap(),
            &Currency::from_str("$0.00").unwrap(),
            BooleanOperation::GT,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            &Currency::from_str("$0.00").unwrap(),
            &Currency::from_str("$0.00").unwrap(),
            BooleanOperation::LTE,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            &Currency::from_str("$0.00").unwrap(),
            &Currency::from_str("$0.00").unwrap(),
            BooleanOperation::GTE,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            &Currency::from_str("$0.00").unwrap(),
            &Currency::from_str("$0.00").unwrap(),
            BooleanOperation::EQ,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Currency::boolean_op(
            &Currency::from_str("$0.00").unwrap(),
            &Currency::from_str("$0.00").unwrap(),
            BooleanOperation::NEQ,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());
    }

    #[test]
    fn test_to_string() {
        let value = Currency::from_str("$10.00").unwrap();
        assert_eq!(value.to_string(), "$10.00".to_string());

        let value = Currency::from_str("10").unwrap();
        assert_eq!(value.to_string(), "10".to_string());

        let value = Currency::from_str("¥10").unwrap();
        assert_eq!(value.to_string(), "¥10".to_string());

        let value = Currency::new(CurrencyInner::new(None, 5, Fixed::from(Dec!(10.123456789))));
        assert_eq!(value.to_string(), "10.12346".to_string());
    }

    #[test]
    fn test_from() {
        assert_eq!(
            Currency::try_from(Value::from(10)).unwrap(),
            Currency::from_fixed(Fixed::from(Dec!(10)))
        );
        assert_eq!(
            Currency::try_from(Value::from(10.0)).unwrap(),
            Currency::from_fixed(Fixed::from(Dec!(10)))
        );
        assert_eq!(
            Currency::try_from(Value::from(Dec!(10.0))).unwrap(),
            Currency::from_fixed(Fixed::from(Dec!(10.0)))
        );
        assert_eq!(
            Currency::try_from(Value::from(true)).unwrap(),
            Currency::from_fixed(Fixed::from(Dec!(1)))
        );

        // string should fail
        assert!(Currency::try_from(Value::from("")).is_err());

        // array with 1 element
        let value = Value::from(vec![Value::from(10)]);
        assert_eq!(
            Currency::try_from(value).unwrap(),
            Currency::from_fixed(Fixed::from(Dec!(10)))
        );

        // array with 2 elements should fail
        let value = Value::from(vec![Value::from(10), Value::from(10)]);
        assert!(Currency::try_from(value).is_err());

        // object with 1 element
        let value = Value::try_from(vec![("a".into(), Value::from(10))]).unwrap();
        assert_eq!(
            Currency::try_from(value).unwrap(),
            Currency::from_fixed(Fixed::from(Dec!(10)))
        );

        // object with 2 elements should fail
        let value = Value::try_from(vec![
            ("a".into(), Value::from(10)),
            ("b".into(), Value::from(10)),
        ])
        .unwrap();
        assert!(Currency::try_from(value).is_err());
    }

    #[test]
    fn test_parse() {
        let value = Currency::from_str("$10.00").unwrap();
        assert_eq!(value.symbol(), &Some("$".to_string()));
        assert_eq!(value.precision(), 2);
        assert_eq!(*value.value().inner(), Dec!(10.00));

        let value = Currency::from_str("10").unwrap();
        assert_eq!(value.symbol(), &None);
        assert_eq!(value.precision(), 0);
        assert_eq!(*value.value().inner(), Dec!(10));

        let value = Currency::from_str("¥10").unwrap();
        assert_eq!(value.symbol(), &Some("¥".to_string()));
        assert_eq!(value.precision(), 0);
        assert_eq!(*value.value().inner(), Dec!(10));
    }
}
