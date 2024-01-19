//! Range type
//!
//! This type is a wrapper around an inclusive range
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `min..max`
//!
use crate::{
    operations::{BooleanOperation, BooleanOperationExt, IndexingOperationExt},
    types::*,
    Error, Value, ValueTrait, ValueType,
};
use serde::{Deserialize, Serialize};
use std::{ops::RangeInclusive, str::FromStr};

/// Inner type of `Range`
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

        if start > end {
            return Err(Error::InvalidRange);
        }

        Ok(Range::new(*start.inner()..=*end.inner()))
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

impl BooleanOperationExt for Range {
    fn boolean_op(
        left: &Self,
        right: &Self,
        operation: BooleanOperation,
    ) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        let left = left.inner().clone();
        let right = right.inner().clone();

        let left_size = left.end() - left.start();
        let right_size = right.end() - right.start();

        match operation {
            BooleanOperation::And => Ok(Bool::from(left_size != 0 && right_size != 0)),
            BooleanOperation::Or => Ok(Bool::from(left_size != 0 || right_size != 0)),
            BooleanOperation::EQ => Ok(Bool::from(left == right)),
            BooleanOperation::NEQ => Ok(Bool::from(left != right)),
            BooleanOperation::LT => Ok(Bool::from(left_size < right_size)),
            BooleanOperation::GT => Ok(Bool::from(left_size > right_size)),
            BooleanOperation::LTE => Ok(Bool::from(left_size <= right_size)),
            BooleanOperation::GTE => Ok(Bool::from(left_size >= right_size)),
            BooleanOperation::Not => Ok(Bool::from(left_size == 0)),
        }
        .and_then(|b| Ok(Value::from(b)))
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Self::boolean_op(self, self, BooleanOperation::Not)
    }
}

impl IndexingOperationExt for Range {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        let index = *index.as_a::<Int>()?.inner();
        let offset = if index < 0 {
            *self.inner().end() + index
        } else {
            *self.inner().start() + index
        };

        if !self.inner().contains(&offset) {
            Err(Error::Index {
                key: index.to_string(),
            })
        } else {
            Ok(Value::from(offset))
        }
    }

    fn get_indices(&self, index: &Value) -> Result<Value, Error> {
        if index.is_a(ValueType::Range) {
            let indices = index.as_a::<Range>()?;
            let values = indices
                .inner()
                .clone()
                .map(|i| self.get_index(&Value::from(i)))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::from(values))
        } else {
            let indices = index.as_a::<Array>()?;
            let values = indices
                .inner()
                .iter()
                .map(|i| self.get_index(i))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::from(values))
        }
    }
}

map_value!(
    from = Range,
    handle_into = Value::Range,
    handle_from = |v: Value| {
        match v {
            Value::Range(v) => Ok(v),
            _ => Err(Error::ValueConversion {
                src_type: v.own_type(),
                dst_type: ValueType::Range,
            }),
        }
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_str() {
        assert_eq!(Range::new(0..=10).to_string(), "0..10");
        assert_eq!(Range::new(0..=0).to_string(), "0..0");

        assert_eq!(Range::from_str("0..10").unwrap(), Range::new(0..=10));
        assert_eq!(Range::from_str("0..").is_err(), true);
        assert_eq!(Range::from_str("..10").is_err(), true);
        assert_eq!(Range::from_str("..").is_err(), true);
        assert_eq!(Range::from_str("-1..-2").is_err(), true);
        assert_eq!(Range::from_str("-2..-1").is_err(), false);
    }
}
