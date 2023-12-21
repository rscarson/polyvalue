//! Currency inner type
//!
//! This is a wrapper around `Fixed` that adds a currency symbol and a precision
//!
use crate::{types::*, Error, ValueTrait};
use fpdec::Decimal;
use serde::{Deserialize, Serialize};

trait RoundToPrecision {
    fn round_to_precision(&self, precision: u32) -> Self;
}
impl RoundToPrecision for Decimal {
    fn round_to_precision(&self, precision: u32) -> Self {
        let precision_10s = 10u32.pow(precision);
        let mut value = self * precision_10s;
        value = value.floor();
        value = value / precision_10s;

        value
    }
}
impl RoundToPrecision for Fixed {
    fn round_to_precision(&self, precision: u32) -> Self {
        Self::from(self.inner().round_to_precision(precision))
    }
}

/// Inner type of `Currency`
/// This is a wrapper around `Fixed` that adds a currency symbol and a precision
#[derive(Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug)]
pub struct CurrencyInner {
    symbol: Option<String>,
    precision: u32,
    value: Fixed,
}
impl CurrencyInner {
    /// Create a new `Currency` from a `Fixed`
    pub fn from_fixed(value: Fixed) -> Self {
        Self::new(None, value.inner().n_frac_digits() as u32, value)
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
        Self::new(Some("¥".to_string()), 2, value)
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
        Self::new(Some("元".to_string()), 2, value)
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
    pub fn new(symbol: Option<String>, precision: u32, value: Fixed) -> Self {
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

    /// Get the value of this `Currency`
    pub fn value(&self) -> &Fixed {
        &self.value
    }

    /// Set the value of this `Currency`
    pub fn set_value(&mut self, value: Fixed) {
        self.value = value.round_to_precision(self.precision);
    }

    /// Get the precision of this `Currency`
    pub fn precision(&self) -> u32 {
        self.precision
    }

    /// Set the precision of this `Currency`
    pub fn set_precision(&mut self, precision: u32) {
        self.precision = precision;
    }

    /// Resolve differences in currencies
    /// If the symbols are different, they will be stripped
    /// The precision will be set to the highest precision
    ///
    /// This is used for operations
    pub fn resolve(&self, other: &Self) -> (Self, Self) {
        let mut left = self.clone();
        let mut right = other.clone();

        if left.symbol != right.symbol {
            left.symbol = None;
            right.symbol = None;
        }

        let precision = left.precision.max(right.precision);
        left.precision = precision;
        right.precision = precision;

        left.value = left.value.round_to_precision(precision);
        right.value = right.value.round_to_precision(precision);

        (left, right)
    }
}

impl std::fmt::Display for CurrencyInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol = self.symbol.clone().unwrap_or_default();
        let value = self.value.inner();
        let precision = self.precision;

        write!(f, "{}{:.*}", symbol, precision as usize, value)
    }
}

impl PartialEq for CurrencyInner {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

const RECOGNIZED_SYMBOLS: [&str; 9] = ["$", "€", "£", "¥", "₹", "₽", "元", "₩", "kr"];
impl std::str::FromStr for CurrencyInner {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut symbol = None;
        let mut value = s.to_string();

        for recognized_symbol in RECOGNIZED_SYMBOLS.iter() {
            if value.starts_with(recognized_symbol) {
                symbol = Some(recognized_symbol.to_string());
                value = value.replace(recognized_symbol, "");
                break;
            }
        }

        let value = Fixed::from_str(&value)?;
        let precision = value.inner().n_frac_digits() as u32;

        Ok(Self::new(symbol, precision, value))
    }
}
