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
    Error, InnerValue, Value, ValueTrait, ValueType,
};
use serde::{Deserialize, Serialize};
use std::ops::RangeInclusive;

type RangeIndex = <int::I64 as ValueTrait>::Inner;

/// Inner type of `Range`
pub type RangeInner = RangeInclusive<RangeIndex>;

/// Subtype of `Value` that represents a range
#[derive(PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct Range(RangeInner);
impl_value!(Range, RangeInner, |v: &Self| format!(
    "{}..{}",
    v.inner().start(),
    v.inner().end()
));

impl Range {
    /// Length of the range
    pub fn len(&self) -> RangeIndex {
        self.inner().end() - self.inner().start()
    }
}

//
// Trait implementations
//

impl PartialOrd for Range {
    fn partial_cmp(&self, other: &Range) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
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
    fn boolean_op(self, right: Self, operation: BooleanOperation) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        let left = self.into_inner();
        let right = right.into_inner();

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
        }
        .map(Value::from)
    }

    fn boolean_not(self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        let left = self.into_inner();
        let left_size = left.end() - left.start();
        Ok(Value::from(left_size == 0))
    }
}

impl ArithmeticOperationExt for Range {
    fn arithmetic_op(self, _: Self, operation: ArithmeticOperation) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Err(Error::UnsupportedOperation {
            operation: operation.to_string(),
            actual_type: ValueType::Range,
        })
    }

    fn arithmetic_neg(self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Err(Error::UnsupportedOperation {
            operation: "negation".to_string(),
            actual_type: ValueType::Range,
        })
    }
}

impl IndexingOperationExt for Range {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        let index = *index.clone().as_a::<I64>()?.inner();
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
            let indices = index.clone().as_a::<Range>()?;
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
            let indices = index.clone().as_a::<Array>()?;
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
                let pattern = pattern.clone().as_a::<Array>()?;
                for value in pattern.inner().iter() {
                    let i = *value.clone().as_a::<I64>()?.inner();
                    if !container.inner().contains(&i) {
                        return Ok(false.into());
                    }
                }
                true
            }
            MatchingOperation::StartsWith => {
                let pattern = pattern.clone().as_a::<Range>()?;
                pattern.start() == container.start() && pattern.end() <= container.end()
            }
            MatchingOperation::EndsWith => {
                let pattern = pattern.clone().as_a::<Range>()?;
                pattern.end() == container.end() && pattern.start() >= container.start()
            }
            MatchingOperation::Matches => {
                let pattern = pattern.clone().as_a::<Range>()?;
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
    handle_into = (v) { Value::range(v) },
    handle_from = (v) {
        match v.inner() {
            InnerValue::Range(v) => Ok(v.clone()),
            InnerValue::Array(v) => {
                if v.len() == 2 {
                    let start = v.get_index(&0.into())?.clone().as_a::<I64>()?;
                    let end = v.get_index(&1.into())?.clone().as_a::<I64>()?;
                    Ok(Range::new(*start.inner()..=*end.inner()))
                } else {
                    Err(Error::ValueConversion {
                        src_type: ValueType::Array,
                        dst_type: ValueType::Range,
                    })
                }
            }
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
    fn test_match() {
        assert_eq!(
            Range::matching_op(
                &Range::new(0..=10),
                &Range::new(0..=10).into(),
                MatchingOperation::Matches
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::matching_op(
                &Range::new(0..=10),
                &Range::new(0..=11).into(),
                MatchingOperation::Matches
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::matching_op(
                &Range::new(0..=10),
                &Range::new(0..=11).into(),
                MatchingOperation::Contains
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::matching_op(
                &Range::new(0..=10),
                &Range::new(0..=10).into(),
                MatchingOperation::Contains
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::matching_op(
                &Range::new(0..=10),
                &Range::new(0..=10).into(),
                MatchingOperation::StartsWith
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::matching_op(
                &Range::new(0..=10),
                &Range::new(0..=10).into(),
                MatchingOperation::EndsWith
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::matching_op(
                &Range::new(0..=10),
                &Range::new(1..=10).into(),
                MatchingOperation::StartsWith
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::matching_op(
                &Range::new(0..=10),
                &Range::new(1..=10).into(),
                MatchingOperation::EndsWith
            )
            .unwrap(),
            true.into()
        );
    }

    #[test]
    fn test_str() {
        assert_eq!(Range::new(0..=10).to_string(), "0..10");
        assert_eq!(Range::new(0..=0).to_string(), "0..0");
    }

    #[test]
    fn test_from() {
        assert_eq!(Range::from(0..=10), Range::new(0..=10));
        Range::try_from(Value::from(vec![0])).unwrap_err();
        Range::try_from(Value::try_from(vec![(0, 0)]).unwrap()).unwrap_err();
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
            Value::i64(3)
        );
        assert_eq!(
            Range::new(1..=10).get_index(&Value::from(-1)).unwrap(),
            Value::i64(10)
        );

        assert_eq!(
            Range::new(1..=10).get_indices(&Value::from(0..=2)).unwrap(),
            vec![Value::i64(1), Value::i64(2), Value::i64(3),].into()
        );
        assert_eq!(
            Range::new(1..=10)
                .get_indices(&Value::from(vec![0, 2]))
                .unwrap(),
            vec![Value::i64(1), Value::i64(3),].into()
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
            Range::boolean_op(Range::new(0..=10), Range::new(0..=10), BooleanOperation::EQ)
                .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(Range::new(0..=10), Range::new(0..=11), BooleanOperation::EQ)
                .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::boolean_op(
                Range::new(0..=10),
                Range::new(0..=11),
                BooleanOperation::NEQ
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(Range::new(0..=10), Range::new(0..=11), BooleanOperation::LT)
                .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(
                Range::new(0..=10),
                Range::new(0..=11),
                BooleanOperation::LTE
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(Range::new(0..=10), Range::new(0..=11), BooleanOperation::GT)
                .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::boolean_op(
                Range::new(0..=10),
                Range::new(0..=11),
                BooleanOperation::GTE
            )
            .unwrap(),
            false.into()
        );
        assert_eq!(
            Range::boolean_op(
                Range::new(0..=10),
                Range::new(0..=11),
                BooleanOperation::And
            )
            .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_op(Range::new(0..=10), Range::new(0..=11), BooleanOperation::Or)
                .unwrap(),
            true.into()
        );
        assert_eq!(
            Range::boolean_not(Range::new(0..=10)).unwrap(),
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
