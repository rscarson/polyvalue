use crate::Error;
use fpdec::{CheckedAdd, CheckedDiv, CheckedMul, CheckedRem, CheckedSub, Decimal, Round};
use serde::{Deserialize, Serialize};
use std::{ops::Deref, str::FromStr};

/// Generates a Fixed from a decimal literal
///
/// # Example
/// ```rust
/// use polyvalue::{fpdec::Decimal, fixed};
/// use polyvalue::types::Fixed;
/// let value = fixed!(1.0);
/// ```
#[macro_export]
macro_rules! fixed {
    ($value:expr) => {
        Fixed::from(fpdec::Dec!($value))
    };
}

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Serialize, Deserialize, Default)]
pub struct BoxedDecimal(Box<Decimal>);
impl BoxedDecimal {
    pub fn new(value: Decimal) -> Self {
        Self(Box::new(value))
    }

    pub fn inner(&self) -> &Decimal {
        &self.0
    }

    pub fn inner_mut(&mut self) -> &mut Decimal {
        &mut self.0
    }

    pub fn n_frac_digits(&self) -> u8 {
        self.0.n_frac_digits()
    }

    pub fn trunc(&self) -> Self {
        Self::new(self.0.trunc())
    }

    pub fn coefficient(&self) -> i128 {
        self.0.coefficient()
    }
}

impl Into<f64> for BoxedDecimal {
    fn into(self) -> f64 {
        (*self.0).into()
    }
}

impl From<Decimal> for BoxedDecimal {
    fn from(value: Decimal) -> Self {
        Self::new(value)
    }
}

impl FromStr for BoxedDecimal {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(s.parse::<Decimal>()?))
    }
}

impl std::fmt::Display for BoxedDecimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::fmt::Debug for BoxedDecimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl CheckedAdd for BoxedDecimal {
    type Output = Option<Self>;
    fn checked_add(self, rhs: Self) -> Self::Output {
        self.0.checked_add(*rhs.0).map(Self::new)
    }
}
impl CheckedSub for BoxedDecimal {
    type Output = Option<Self>;
    fn checked_sub(self, rhs: Self) -> Self::Output {
        self.0.checked_sub(*rhs.0).map(Self::new)
    }
}
impl CheckedMul for BoxedDecimal {
    type Output = Option<Self>;
    fn checked_mul(self, rhs: Self) -> Self::Output {
        self.0.checked_mul(*rhs.0).map(Self::new)
    }
}
impl CheckedDiv for BoxedDecimal {
    type Output = Option<Self>;
    fn checked_div(self, rhs: Self) -> Self::Output {
        self.0.checked_div(*rhs.0).map(Self::new)
    }
}
impl CheckedRem for BoxedDecimal {
    type Output = Option<Self>;
    fn checked_rem(self, rhs: Self) -> Self::Output {
        self.0.checked_rem(*rhs.0).map(Self::new)
    }
}
impl Round for BoxedDecimal {
    fn round(self, n_frac_digits: i8) -> Self {
        Self::new(self.0.round(n_frac_digits))
    }

    fn checked_round(self, n_frac_digits: i8) -> Option<Self> {
        self.0.checked_round(n_frac_digits).map(Self::new)
    }
}
impl std::ops::Neg for BoxedDecimal {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self::new(-*(self.0))
    }
}

impl Deref for BoxedDecimal {
    type Target = Decimal;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
