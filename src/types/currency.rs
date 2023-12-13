use crate::{operations::*, types::*, Value, ValueTrait};
use serde::{Deserialize, Serialize};

/// Inner type of `Currency`
#[derive(Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug)]
pub struct CurrencyInner {
    symbol: Option<String>,
    value: Fixed,
}
impl CurrencyInner {
    /// Create a new `Currency` with a symbol
    pub fn new(symbol: Option<String>, value: Fixed) -> Self {
        Self { symbol, value }
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
        self.value = value;
    }
}

impl PartialEq for CurrencyInner {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

/// Subtype of `Value` that represents a currency
/// This is a wrapper around `Fixed` that adds a currency symbol
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug)]
pub struct Currency(CurrencyInner);
impl_value!(Currency, CurrencyInner, |v: &Self| {
    let symbol = v.inner().symbol().clone().unwrap_or_default();
    let value = v.inner().value().to_string();
    format!("{}{}", symbol, value)
});

map_value!(
    from = Currency,
    handle_into = |v: Currency| Value::Currency(v),
    handle_from = |v: Value| {
        let value = Fixed::try_from(v)?;
        Ok(Currency::without_symbol(value))
    }
);

map_type!(Array, Currency);
map_type!(Object, Currency);
map_type!(Int, Currency);
map_type!(Float, Currency);
map_type!(Fixed, Currency);
map_type!(Bool, Currency);
map_type!(Str, Currency);

impl Currency {
    /// Create a new `Currency` with a symbol
    pub fn with_symbol(symbol: Option<String>, value: Fixed) -> Self {
        Self(CurrencyInner::new(symbol, value))
    }

    /// Create a new `Currency` without a symbol
    pub fn without_symbol(value: Fixed) -> Self {
        Self(CurrencyInner::new(None, value))
    }

    /// Get the symbol of this `Currency`
    pub fn symbol(&self) -> &Option<String> {
        self.inner().symbol()
    }

    /// Set the symbol of this `Currency`
    pub fn set_symbol(&mut self, symbol: Option<String>) {
        self.inner_mut().set_symbol(symbol)
    }
}

impl ArithmeticOperationExt for Currency {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let symbol = left.symbol().clone();
        let left = left.inner().value();
        let right = right.inner().value();
        let result = Fixed::arithmetic_op(left, right, operation)?;
        Ok(Currency::with_symbol(symbol, result))
    }
}
