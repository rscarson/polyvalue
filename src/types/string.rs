//! String type
//!
//! This type is a wrapper around `String`
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::ops::Range;

/// Subtype of `Value` that represents a string
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug)]
pub struct Str(String);
impl_value!(Str, String, |v: &Self| v.inner().clone());

impl From<&str> for Str {
    fn from(value: &str) -> Self {
        <Str>::new(value.to_string())
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        <Str>::new(value.to_string()).into()
    }
}

impl Str {
    /// Maps a range of values to a range of bytes in a string coresponding to the same characters
    /// This is necessary because the string is UTF-8 encoded
    /// Can fail if the range is out of bounds, or if the range is not a valid integer range
    fn map_range_to_bytes(&self, range: Range<&Value>) -> Result<Range<usize>, Error> {
        let mut range = *Int::try_from(range.start.clone())?.inner() as usize
            ..*Int::try_from(range.end.clone())?.inner() as usize;

        // Get the byte-index of the nth character of self.inner()
        // This is necessary because the string is UTF-8 encoded
        // and we need to get the nth character, not the nth byte
        let mut byte_index = 0;
        for _ in 0..range.start {
            byte_index += self
                .inner()
                .get(byte_index..)
                .ok_or(Error::Index {
                    key: range.start.to_string(),
                })?
                .chars()
                .next()
                .ok_or(Error::Index {
                    key: range.start.to_string(),
                })?
                .len_utf8();
        }
        range.start = byte_index;

        // and the start of the next
        let mut byte_index = 0;
        for _ in 0..range.end + 1 {
            byte_index += self
                .inner()
                .get(byte_index..)
                .ok_or(Error::Index {
                    key: range.end.to_string(),
                })?
                .chars()
                .next()
                .ok_or(Error::Index {
                    key: range.end.to_string(),
                })?
                .len_utf8();
        }
        range.end = byte_index - 1;

        Ok(range)
    }
    /// String indexing
    /// Returns a substring
    ///
    /// Although this looks like the IndexingOperationExt trait, it is not
    /// because it returns a string instead of a value
    pub fn get_index(&self, index: Range<&Value>) -> Result<&str, crate::Error> {
        let range = self.map_range_to_bytes(index)?;
        self.inner()
            .get(range.start..=range.end)
            .ok_or(Error::Index {
                key: format!("{}..{}", range.start, range.end),
            })
    }

    /// Mutable string indexing
    /// Returns a mutable substring
    ///
    /// Although this looks like the IndexingOperationExt trait, it is not
    /// because it returns a string instead of a value
    pub fn get_index_mut(&mut self, index: Range<&Value>) -> Result<&mut str, crate::Error> {
        let range = self.map_range_to_bytes(index)?;
        self.inner_mut()
            .get_mut(range.start..=range.end)
            .ok_or(Error::Index {
                key: format!("{}..{}", range.start, range.end),
            })
    }

    /// Replace a set of characters in the string
    ///
    /// Although this looks like the IndexingOperationExt trait, it is not
    /// because it returns a string instead of a value
    pub fn set_index(&mut self, index: Range<&Value>, value: Value) -> Result<(), crate::Error> {
        let range = *Int::try_from(index.start.clone())?.inner() as usize
            ..*Int::try_from(index.end.clone())?.inner() as usize;

        let value = Str::try_from(value)?.inner().clone();

        let prefix = if range.start == 0 {
            ""
        } else {
            self.get_index(&0.into()..&(range.start - 1).into())?
        };

        let suffix = if range.end == self.inner().chars().count() - 1 {
            ""
        } else {
            self.get_index(&(range.end + 1).into()..&(self.inner().chars().count() - 1).into())?
        };

        *self.inner_mut() = format!("{}{}{}", prefix, value, suffix);
        Ok(())
    }
}

map_value!(
    from = Str,
    handle_into = |v: Str| Value::String(v),
    handle_from = |v: Value| match v {
        Value::String(v) => Ok(v),
        _ => Ok(Str::from(v.to_string())),
    }
);

map_type!(Bool, Str);
map_type!(Int, Str);
map_type!(Float, Str);
map_type!(Fixed, Str);
map_type!(Currency, Str);
map_type!(Array, Str);
map_type!(Object, Str);

impl ArithmeticOperationExt for Str {
    fn arithmetic_op(
        left: &Self,
        right: &Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, crate::Error> {
        let left = left.inner().to_string();
        let right = right.inner().to_string();
        let result = match operation {
            ArithmeticOperation::Add => left + right.as_str(),
            ArithmeticOperation::Subtract => left.replace(&right, ""),
            _ => Err(Error::UnsupportedOperation {
                operation: operation,
                actual_type: ValueType::String,
            })?,
        };
        Ok(result.into())
    }

    fn arithmetic_neg(&self) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        Str::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
    }
}

impl BooleanOperationExt for Str {
    fn boolean_op(left: &Self, right: &Self, operation: BooleanOperation) -> Result<Value, Error> {
        let result = match operation {
            BooleanOperation::And => !left.inner().is_empty() && !right.inner().is_empty(),
            BooleanOperation::Or => !left.inner().is_empty() || !right.inner().is_empty(),

            BooleanOperation::LT => *left.inner() < *right.inner(),
            BooleanOperation::GT => *left.inner() > *right.inner(),
            BooleanOperation::LTE => *left.inner() <= *right.inner(),
            BooleanOperation::GTE => *left.inner() >= *right.inner(),
            BooleanOperation::EQ => *left.inner() == *right.inner(),
            BooleanOperation::NEQ => *left.inner() != *right.inner(),
            BooleanOperation::Not => left.inner().is_empty(),
        };

        Ok(result.into())
    }

    fn boolean_not(&self) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        Str::boolean_op(self, &self.clone(), BooleanOperation::Not)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_indexing() {
        // normal string
        let s = Str::from("Hello, world!");
        assert_eq!(s.get_index(&0.into()..&1.into()).unwrap(), "He");

        // Bad and scary unicode string, with multibyte chars at the start
        let s = Str::from("👋🌎");
        assert_eq!(s.get_index(&0.into()..&0.into()).unwrap(), "👋");

        let mut s = Str::from("S👋🌎");
        s.set_index(&1.into()..&1.into(), "B".into()).unwrap();
        assert_eq!(s, "SB🌎".into());

        let mut s = Str::from("S👋🌎");
        s.set_index(&0.into()..&1.into(), "B".into()).unwrap();
        assert_eq!(s, "B🌎".into());

        let mut s = Str::from("S👋🌎");
        s.set_index(&0.into()..&0.into(), "B".into()).unwrap();
        assert_eq!(s, "B👋🌎".into());

        let mut s = Str::from("S👋🌎");
        s.set_index(&2.into()..&2.into(), "B".into()).unwrap();
        assert_eq!(s, "S👋B".into());
    }
}
