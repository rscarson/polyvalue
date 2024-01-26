//! Range type
//!
//! This type is a wrapper around an inclusive range
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `min..max`
//!
use crate::{
    operations::{
        ArithmeticOperation, ArithmeticOperationExt, BooleanOperation, BooleanOperationExt,
        IndexingOperationExt, MatchingOperation, MatchingOperationExt,
    },
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

impl Range {
    /// Length of the range
    pub fn len(&self) -> IntInner {
        self.inner().end() - self.inner().start()
    }
}

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
        self.partial_cmp(other).unwrap()
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

impl ArithmeticOperationExt for Range {
    fn arithmetic_op(
        _: &Self,
        _: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        return Err(Error::UnsupportedOperation {
            operation: operation.to_string(),
            actual_type: ValueType::Range,
        });
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Self::arithmetic_op(self, self, ArithmeticOperation::Negate)
    }

    fn is_operator_supported(&self, _: &Self, _: ArithmeticOperation) -> bool {
        false
    }
}

impl IndexingOperationExt for Range {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        let index = *index.as_a::<Int>()?.inner();
        let offset = if index < 0 {
            *self.inner().end() + index + 1
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
            if self.len() < indices.len() {
                return Err(Error::Index {
                    key: index.to_string(),
                });
            }

            let offset = *self.inner().start();
            let new_range =
                Range::new((indices.inner().start() + offset)..=(indices.inner().end() + offset));
            let results = Array::try_from(new_range)?;
            Ok(results.into())
        } else {
            let indices = index.as_a::<Array>()?;
            let mut container = Array::prealloc_range_conversion(indices.len())?;
            for i in indices.inner().iter() {
                container.push(self.get_index(i)?);
            }
            Ok(container.into())
        }
    }
}

impl MatchingOperationExt for Range {
    fn matching_op(
        container: &Self,
        pattern: &Value,
        operation: MatchingOperation,
    ) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        let result = match operation {
            MatchingOperation::Contains => {
                let pattern = pattern.as_a::<Array>()?;
                for value in pattern.inner().iter() {
                    let i = *value.as_a::<Int>()?.inner();
                    if !container.inner().contains(&i) {
                        return Ok(false.into());
                    }
                }
                true
            }
            MatchingOperation::StartsWith => {
                let pattern = pattern.as_a::<Range>()?;
                pattern.start() == container.start() && pattern.end() <= container.end()
            }
            MatchingOperation::EndsWith => {
                let pattern = pattern.as_a::<Range>()?;
                pattern.end() == container.end() && pattern.start() >= container.start()
            }
            MatchingOperation::Matches => {
                let pattern = pattern.as_a::<Range>()?;
                pattern == *container
            }

            // Handled by Value
            _ => false,
        };

        Ok(result.into())
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

overload_operator!(Range, deref);

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

    #[test]
    fn test_from() {
        assert_eq!(Range::from(0..=10), Range::new(0..=10));
        Range::try_from(Value::from(vec![0.into()])).unwrap_err();
        Range::try_from(Value::try_from(vec![(0.into(), 0.into())]).unwrap()).unwrap_err();
        Range::try_from(Value::from(0)).unwrap_err();
        Range::try_from(Value::from(0.0)).unwrap_err();
        Range::try_from(Value::from("")).unwrap_err();
    }

    #[test]
    fn test_indexing() {
        Range::new(1..=10).get_index(&Value::from(10)).unwrap_err();
        Range::new(1..=10).get_index(&Value::from(-20)).unwrap_err();
        assert_eq!(
            Range::new(1..=10).get_index(&Value::from(2)).unwrap(),
            3.into()
        );
        assert_eq!(
            Range::new(1..=10).get_index(&Value::from(-1)).unwrap(),
            10.into()
        );

        assert_eq!(
            Range::new(1..=10).get_indices(&Value::from(0..=2)).unwrap(),
            vec![1.into(), 2.into(), 3.into()].into()
        );
        assert_eq!(
            Range::new(1..=10)
                .get_indices(&Value::from(vec![0.into(), 2.into()]))
                .unwrap(),
            vec![1.into(), 3.into()].into()
        );

        Range::new(0..=9999999999)
            .get_indices(&Value::from(0..=999999999))
            .unwrap_err();

        Range::new(0..=10)
            .get_indices(&Value::from(0..=11))
            .unwrap_err();
    }

    #[test]
    fn test_boolean() {
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=10),
                BooleanOperation::EQ
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=11),
                BooleanOperation::EQ
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=11),
                BooleanOperation::NEQ
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=11),
                BooleanOperation::LT
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=11),
                BooleanOperation::LTE
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=11),
                BooleanOperation::GT
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=11),
                BooleanOperation::GTE
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=11),
                BooleanOperation::And
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=11),
                BooleanOperation::Or
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(
                &Range::new(0..=10),
                &Range::new(0..=11),
                BooleanOperation::Not
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::boolean_not(&Range::new(0..=10)).unwrap(),
            false.into()
        );
    }

    #[test]
    fn test_ord() {
        assert_eq!(
            Range::new(0..=10).cmp(&Range::new(0..=10)),
            std::cmp::Ordering::Equal
        );
        assert_eq!(
            Range::new(0..=10).cmp(&Range::new(0..=11)),
            std::cmp::Ordering::Less
        );
        assert_eq!(
            Range::new(0..=10).cmp(&Range::new(0..=9)),
            std::cmp::Ordering::Greater
        );
        assert_eq!(
            Range::default().cmp(&Range::new(0..=9)),
            std::cmp::Ordering::Less
        );
    }
}
