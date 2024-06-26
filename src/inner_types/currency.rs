//! Currency inner type
//!
//! This is a wrapper around `Fixed` that adds a currency symbol and a precision
//!
use crate::is_currency::IsCurrency;
use crate::operations::ArithmeticOperationExt;
use crate::{types::*, Error, ValueTrait};
use fpdec::Round;
use serde::{Deserialize, Serialize};

trait RoundToPrecision {
    fn round_to_precision(&self, precision: i8) -> Self;
}
impl RoundToPrecision for Fixed {
    fn round_to_precision(&self, precision: i8) -> Self {
        Self::from(self.inner().clone().round(precision))
    }
}

/// Inner type of `Currency`
/// This is a wrapper around `Fixed` that adds a currency symbol and a precision
#[derive(Eq, PartialOrd, PartialEq, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct CurrencyInner {
    symbol: Option<String>,
    precision: i8,
    value: Fixed,
}
impl CurrencyInner {
    /// Create a new `Currency` from a `Fixed`
    /// Caps precision at 5, to prevent float silliness
    pub fn from_fixed(value: Fixed) -> Self {
        Self::new(None, value.inner().n_frac_digits() as i8, value)
    }

    /// Creates a new dollar currency
    pub fn as_dollars(value: Fixed) -> Self {
        Self::new(Some("$".to_string()), 2, value)
    }

    /// Create a new euro currency
    pub fn as_euros(value: Fixed) -> Self {
        Self::new(Some("€".to_string()), 2, value)
    }

    /// Create a new pound currency
    pub fn as_pounds(value: Fixed) -> Self {
        Self::new(Some("£".to_string()), 2, value)
    }

    /// Create a new yen currency
    pub fn as_yen(value: Fixed) -> Self {
        Self::new(Some("¥".to_string()), 0, value)
    }

    /// Create a new rupee currency
    pub fn as_rupees(value: Fixed) -> Self {
        Self::new(Some("₹".to_string()), 2, value)
    }

    /// Create a new rubles currency
    pub fn as_rubles(value: Fixed) -> Self {
        Self::new(Some("₽".to_string()), 2, value)
    }

    /// Create a new yuan currency
    pub fn as_yuan(value: Fixed) -> Self {
        Self::new(Some("¥".to_string()), 2, value)
    }

    /// Create a new won currency
    pub fn as_won(value: Fixed) -> Self {
        Self::new(Some("₩".to_string()), 2, value)
    }

    /// Create a new kr currency
    pub fn as_krona(value: Fixed) -> Self {
        Self::new(Some("kr".to_string()), 2, value)
    }

    /// Create a new `Currency` with a symbol
    pub fn new(symbol: Option<String>, precision: i8, value: Fixed) -> Self {
        Self {
            symbol,
            precision,
            value: value.round_to_precision(precision),
        }
    }

    /// Get the symbol of this `Currency`
    pub fn symbol(&self) -> &Option<String> {
        &self.symbol
    }

    /// Set the symbol of this `Currency`
    pub fn set_symbol(&mut self, symbol: Option<String>) {
        self.symbol = symbol;
    }

    /// Return the properties of this value, consuming it
    pub fn into_properties(self) -> (Fixed, i8, Option<String>) {
        (self.value, self.precision, self.symbol)
    }

    /// Return the value of this `Currency`, consuming it
    pub fn into_value(self) -> Fixed {
        self.value
    }

    /// Get the value of this `Currency`
    pub fn value(&self) -> &Fixed {
        &self.value
    }

    /// Set the value of this `Currency`
    pub fn set_value(&mut self, value: Fixed) {
        self.value = value.round_to_precision(self.precision);
    }

    /// Get the precision of this `Currency`
    pub fn precision(&self) -> i8 {
        self.precision
    }

    /// Set the precision of this `Currency`
    pub fn set_precision(&mut self, precision: i8) {
        self.precision = precision;
    }

    /// Resolve differences in currencies
    /// If the symbols are different, they will be stripped
    /// If only one symbol is present, it will be used
    /// The precision will be set to the highest precision
    ///
    /// This is used for operations
    pub fn resolve(mut self, mut other: Self) -> (Self, Self) {
        // resolve symbols
        match (&self.symbol, &other.symbol) {
            (Some(_), None) => other.symbol = self.symbol.clone(),
            (None, Some(_)) => self.symbol = other.symbol.clone(),
            (Some(_), Some(_)) => {
                if self.symbol != other.symbol {
                    self.symbol = None;
                    other.symbol = None;
                }
            }
            (None, None) => {}
        }

        // resolve precision
        let precision = self.precision.max(other.precision);
        self.precision = precision;
        other.precision = precision;

        // round values
        self.value = self.value.round_to_precision(precision);
        other.value = other.value.round_to_precision(precision);

        (self, other)
    }
}

impl ArithmeticOperationExt for CurrencyInner {
    fn arithmetic_op(
        self,
        right: Self,
        operation: crate::operations::ArithmeticOperation,
    ) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        let (left, right) = self.resolve(right);
        let (left, right) = (left.into_properties(), right.into_properties());

        let value = left.0.arithmetic_op(right.0, operation)?;
        Ok(CurrencyInner::new(left.2, left.1, value))
    }

    fn arithmetic_neg(self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        let value = self.value.arithmetic_neg()?;
        Ok(CurrencyInner::new(self.symbol, self.precision, value))
    }
}

impl std::fmt::Display for CurrencyInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol = self.symbol.clone().unwrap_or_default();
        let value = self.value.inner();
        let precision = self.precision;

        write!(f, "{:.*}{}", precision as usize, value, symbol)
    }
}

impl std::fmt::Debug for CurrencyInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol = self.symbol.clone().unwrap_or_default();
        let value = self.value.inner();
        let precision = self.precision;

        write!(f, "{:.*}{}", precision as usize, value, symbol)
    }
}

impl std::str::FromStr for CurrencyInner {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut symbol = None;
        let mut value = s.to_string();

        // Check if the string contains a currency symbol
        if let Some((i, c)) = s.find_currency_symbol() {
            symbol = Some(c.to_string());
            value.remove(i);
        }

        let value = Fixed::from_str(&value)?;
        let precision = value.inner().n_frac_digits() as i8;

        Ok(Self::new(symbol, precision, value))
    }
}

impl From<Fixed> for CurrencyInner {
    fn from(value: Fixed) -> Self {
        Self::from_fixed(value)
    }
}

//
// Test
//

#[cfg(test)]
mod test {
    use crate::Value;

    use super::*;
    use crate::fixed;
    use fpdec::Decimal;
    use std::str::FromStr;

    #[test]
    fn test_resolve() {
        let l = CurrencyInner::from_str("$1.00").unwrap();
        let r = CurrencyInner::from_str("€1.000").unwrap();
        let (l, r) = l.resolve(r);
        assert_eq!(l.to_string(), "1.000");
        assert_eq!(r.to_string(), "1.000");

        let l = CurrencyInner::from_str("1.00$").unwrap();
        let r = CurrencyInner::from_str("1.0").unwrap();
        let (l, r) = l.resolve(r);
        assert_eq!(l.to_string(), "1.00$");
        assert_eq!(r.to_string(), "1.00$");

        let l = CurrencyInner::from_str("1.00").unwrap();
        let r = CurrencyInner::from_str("1").unwrap();
        let (l, r) = l.resolve(r);
        assert_eq!(l.to_string(), "1.00");
        assert_eq!(r.to_string(), "1.00");
    }

    #[test]
    fn test_parse() {
        let mut currency = CurrencyInner::as_dollars(fixed!(1.0));
        currency.set_precision(4);

        let currency = currency.to_string();

        let currency = CurrencyInner::from_str(&currency).unwrap();

        assert_eq!(currency.symbol, Some("$".to_string()));
        assert_eq!(currency.precision, 4);
        assert_eq!(currency.value, fixed!(1.0));
    }

    #[test]
    fn test_float_nonsense() {
        let silly_value = Value::from(2.2);
        let silly_value = CurrencyInner::from(Fixed::try_from(silly_value).unwrap());

        assert_eq!(silly_value.to_string(), "2.2");
        assert_eq!(silly_value.precision, 1);

        let l = Value::from(2.2);
        let r = Value::from(CurrencyInner::from_str("100.00$").unwrap());
        let (l, r) = l.resolve(r).unwrap();
        assert_eq!(l.to_string(), "2.20$");
        assert_eq!(r.to_string(), "100.00$");
    }

    #[test]
    fn test_as_currencies() {
        let fixed = fixed!(1.0);
        assert_eq!(
            CurrencyInner::as_dollars(fixed.clone()).to_string(),
            "1.00$"
        );
        assert_eq!(CurrencyInner::as_euros(fixed.clone()).to_string(), "1.00€");
        assert_eq!(CurrencyInner::as_pounds(fixed.clone()).to_string(), "1.00£");
        assert_eq!(CurrencyInner::as_yen(fixed.clone()).to_string(), "1¥");
        assert_eq!(CurrencyInner::as_rupees(fixed.clone()).to_string(), "1.00₹");
        assert_eq!(CurrencyInner::as_rubles(fixed.clone()).to_string(), "1.00₽");
        assert_eq!(CurrencyInner::as_yuan(fixed.clone()).to_string(), "1.00¥");
        assert_eq!(CurrencyInner::as_won(fixed.clone()).to_string(), "1.00₩");
        assert_eq!(CurrencyInner::as_krona(fixed.clone()).to_string(), "1.00kr");
    }

    #[test]
    fn test_manipulate() {
        let mut currency = CurrencyInner::as_dollars(fixed!(1.0));
        currency.set_precision(4);

        assert_eq!(currency.to_string(), "1.0000$");

        currency.set_symbol(Some("€".to_string()));
        assert_eq!(currency.to_string(), "1.0000€");

        currency.set_value(fixed!(2.0));
        assert_eq!(currency.to_string(), "2.0000€");

        currency.set_precision(2);
        assert_eq!(currency.to_string(), "2.00€");
    }
}
