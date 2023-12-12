use crate::{operations::*, types::*, Value, ValueTrait};
use serde::{Deserialize, Serialize};

/// Inner type of `Currency`
#[derive(Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
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
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Currency(CurrencyInner);
impl_value!(Currency, CurrencyInner);

map_value!(
    from = Currency,
    handle_into = |v: Currency| Value::Currency(v),
    handle_from = |v: Value| match v {
        Value::Currency(v) => Ok(v),
        Value::Int(v) => v.try_into(),
        Value::Float(v) => v.try_into(),
        Value::Fixed(v) => v.try_into(),
        Value::Bool(v) => v.try_into(),
        Value::String(v) => v.try_into(),
        Value::Array(v) => v.try_into(),
        Value::Object(v) => v.try_into(),
    }
);

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
        let left = Fixed::try_from(left.clone())?;
        let right = Fixed::try_from(right.clone())?;
        let result = Fixed::arithmetic_op(&left, &right, operation)?;
        Ok(Currency::with_symbol(symbol, result))
    }
}

//
// Conversion from other types
//

map_type!(into = Bool, from = Currency, |v: Currency| {
    Ok((*v.inner().value().inner() != FixedInner::ZERO).into())
});

map_type!(into = Fixed, from = Currency, |v: Currency| {
    Ok(v.inner().value().clone())
});

map_type!(into = Float, from = Currency, |v: Currency| {
    Ok(v.inner().value().clone().try_into().unwrap())
});

map_type!(into = Int, from = Currency, |v: Currency| {
    let cooef = v.inner().value().inner().trunc().coefficient() as IntInner;
    Ok(cooef.into())
});

map_type!(into = Str, from = Currency, |v: Currency| {
    Ok(format!(
        "{}{}",
        v.inner().symbol.clone().unwrap_or_default(),
        v.inner().value()
    )
    .into())
});

map_type!(into = Array, from = Currency, |v: Currency| {
    Ok(vec![Value::from(v)].into())
});

map_type!(into = Object, from = Currency, |v: Currency| {
    let index = Value::from(Int::new(0));
    let value = Value::from(v);

    // Convert [index, value] into ObjectInner
    let map: ObjectInner = vec![(index, value)].into_iter().collect();

    Ok(map.into())
});
