//! Range type
//!
//! This type is a wrapper around an inclusive range
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `min..max`
//!
use crate::{types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::{ops::RangeInclusive, str::FromStr};

pub type RangeInner = RangeInclusive<IntInner>;

/// Subtype of `Value` that represents a range
#[derive(PartialEq, Eq, Clone, Hash, Serialize, Deserialize, Debug)]
pub struct Range(RangeInner);
impl_value!(Range, RangeInner, |v: &Self| format!(
    "{}..{}",
    v.inner().start(),
    v.inner().end()
));

//
// Trait implementations
//

impl FromStr for Range {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parts = s.split("..");
        let start = parts.next().ok_or(Error::InvalidRange)?;
        let end = parts.next().ok_or(Error::InvalidRange)?;
        let start = start.parse::<Int>()?;
        let end = end.parse::<Int>()?;
        Ok(Range::new(start..=end))
    }
}

impl PartialOrd for Range {
    fn partial_cmp(&self, other: &Range) -> Option<std::cmp::Ordering> {
        (self.inner().end() - self.inner().start())
            .partial_cmp(&(other.inner().end() - other.inner().start()))
    }
}

impl Ord for Range {
    fn cmp(&self, other: &Range) -> std::cmp::Ordering {
        (self.inner().end() - self.inner().start())
            .cmp(&(other.inner().end() - other.inner().start()))
    }
}

impl Default for Range {
    fn default() -> Self {
        Range::new(0..=0)
    }
}

map_value!(
    from = Range,
    handle_into = |v: Range| Value::Range(v),
    handle_from = |v: Value| {
        Err(Error::ValueConversion {
            src_type: v.own_type(),
            dst_type: ValueType::Range,
        })
    }
);

map_type!(Bool, Range);
map_type!(Int, Range);
map_type!(Float, Range);
map_type!(Fixed, Range);
map_type!(Currency, Range);
map_type!(Array, Range);
map_type!(Object, Range);
map_type!(Str, Range);
