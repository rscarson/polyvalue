//! String type
//!
//! This type is a wrapper around `String`
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::{cell::RefCell, ops::Range, rc::Rc};

/// Inner type of `Str`
/// This is a wrapper around `String` which also supports references
/// and mutable references
///
/// This is necessary because we need to be able to return substrings
/// in indexing operations, and we can't do that with a normal string
///
/// NOTE: A lot of &mut self is used here, because we need to be able to
/// solidify references to solid strings for certain operations, notably:
/// - get
/// - get_mut
/// - chars
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum StrInner {
    Direct(String),
    ByRef(Rc<String>),
    ByMut(Rc<RefCell<String>>),
}

impl std::hash::Hash for StrInner {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            StrInner::Direct(v) => v.hash(state),
            StrInner::ByRef(v) => v.hash(state),
            StrInner::ByMut(v) => v.borrow().hash(state),
        }
    }
}

impl From<&str> for StrInner {
    fn from(value: &str) -> Self {
        Self::Direct(value.into())
    }
}

impl From<String> for StrInner {
    fn from(value: String) -> Self {
        Self::Direct(value)
    }
}

impl Default for StrInner {
    fn default() -> Self {
        Self::Direct(String::default())
    }
}

impl Serialize for StrInner {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            StrInner::Direct(v) => serializer.serialize_str(v),
            StrInner::ByRef(v) => serializer.serialize_str(v.as_str()),
            StrInner::ByMut(v) => serializer.serialize_str(v.borrow().as_str()),
        }
    }
}

impl<'de> Deserialize<'de> for StrInner {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Ok(StrInner::Direct(s))
    }
}

impl std::fmt::Display for StrInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StrInner::Direct(v) => write!(f, "{}", v),
            StrInner::ByRef(v) => write!(f, "{}", v),
            StrInner::ByMut(v) => write!(f, "{}", v.borrow()),
        }
    }
}

impl StrInner {
    pub fn new(s: &str) -> Self {
        Self::Direct(s.into())
    }

    pub fn new_ref(s: &str) -> Self {
        Self::ByRef(Rc::new(s.into()))
    }

    pub fn new_mut(s: &mut str) -> Self {
        Self::ByMut(Rc::new(RefCell::new(s.into())))
    }

    pub fn solidify(&mut self) {
        *self = StrInner::Direct(self.to_string());
    }

    pub fn get<I: std::slice::SliceIndex<str>>(&mut self, i: I) -> Option<&I::Output> {
        match self {
            StrInner::Direct(v) => v.get(i),
            _ => {
                self.solidify();
                self.get(i)
            }
        }
    }

    pub fn get_mut<I: std::slice::SliceIndex<str>>(&mut self, i: I) -> Option<&mut I::Output> {
        match self {
            StrInner::Direct(v) => v.get_mut(i),
            _ => {
                self.solidify();
                self.get_mut(i)
            }
        }
    }

    pub fn chars(&mut self) -> std::str::Chars {
        match self {
            StrInner::Direct(v) => v.chars(),
            _ => {
                self.solidify();
                self.chars()
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            StrInner::Direct(v) => v.is_empty(),
            StrInner::ByRef(v) => v.is_empty(),
            StrInner::ByMut(v) => v.borrow().is_empty(),
        }
    }
}

/// Subtype of `Value` that represents a string
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug)]
pub struct Str(StrInner);
impl_value!(Str, StrInner, |v: &Self| v.inner().clone());

impl From<&str> for Str {
    fn from(value: &str) -> Self {
        <Str>::new(value.into())
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        <Str>::new(value.into()).into()
    }
}

impl From<String> for Str {
    fn from(value: String) -> Self {
        <Str>::new(value.into())
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        <Str>::new(value.into()).into()
    }
}

impl Str {
    /// Maps a range of values to a range of bytes in a string coresponding to the same characters
    /// This is necessary because the string is UTF-8 encoded
    /// Can fail if the range is out of bounds, or if the range is not a valid integer range
    fn map_range_to_bytes(&mut self, range: Range<&Value>) -> Result<Range<usize>, Error> {
        let mut range = *Int::try_from(range.start.clone())?.inner() as usize
            ..*Int::try_from(range.end.clone())?.inner() as usize;

        // Get the byte-index of the nth character of self.inner()
        // This is necessary because the string is UTF-8 encoded
        // and we need to get the nth character, not the nth byte
        let mut byte_index = 0;
        for _ in 0..range.start {
            byte_index += self
                .inner_mut()
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
                .inner_mut()
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
    pub fn substr(&mut self, index: Range<&Value>) -> Result<&str, crate::Error> {
        let range = self.map_range_to_bytes(index)?;
        self.inner_mut()
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
    pub fn mut_substr(&mut self, index: Range<&Value>) -> Result<&mut str, crate::Error> {
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
    pub fn set_substr(&mut self, index: Range<&Value>, value: Value) -> Result<(), crate::Error> {
        let range = *Int::try_from(index.start.clone())?.inner() as usize
            ..*Int::try_from(index.end.clone())?.inner() as usize;

        let value = Str::try_from(value)?.inner().clone();

        let prefix = if range.start == 0 {
            "".to_string()
        } else {
            self.substr(&0.into()..&(range.start - 1).into())?
                .to_string()
        };

        let char_count = self.inner_mut().chars().count();
        let suffix = if range.end == char_count - 1 {
            ""
        } else {
            self.substr(&(range.end + 1).into()..&(char_count - 1).into())?
        };

        *self.inner_mut() = format!("{}{}{}", prefix, value, suffix).into();
        Ok(())
    }

    /// Convert an index value to a range, useful for bridging the gap between
    /// the IndexingOperationExt trait and the substr functions
    pub fn index_value_to_range(index: &Value) -> Result<Range<Value>, Error> {
        // Convert index to a range - we will need an array of integers
        let index = index.as_a::<Array>()?;
        let indices = index
            .inner()
            .iter()
            .map(|v| Ok::<IntInner, Error>(*v.as_a::<Int>()?.inner()))
            .collect::<Result<Vec<_>, _>>()?;
        if indices.len() < 1 || indices.len() > 2 {
            Err(Error::Index {
                key: index.to_string(),
            })?;
        } else if indices.len() == 2 && indices[0] > indices[1] {
            Err(Error::Index {
                key: index.to_string(),
            })?;
        }

        Ok(if indices.len() == 1 {
            indices[0].into()..indices[0].into()
        } else {
            indices[0].into()..indices[1].into()
        })
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

//
// Tests
//

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_indexing() {
        // normal string
        let mut s = Str::from("Hello, world!");
        assert_eq!(s.substr(&0.into()..&1.into()).unwrap(), "He");

        // Bad and scary unicode string, with multibyte chars at the start
        let mut s = Str::from("👋🌎");
        assert_eq!(s.substr(&0.into()..&0.into()).unwrap(), "👋");

        let mut s = Str::from("S👋🌎");
        s.set_substr(&1.into()..&1.into(), "B".into()).unwrap();
        assert_eq!(s, "SB🌎".into());

        let mut s = Str::from("S👋🌎");
        s.set_substr(&0.into()..&1.into(), "B".into()).unwrap();
        assert_eq!(s, "B🌎".into());

        let mut s = Str::from("S👋🌎");
        s.set_substr(&0.into()..&0.into(), "B".into()).unwrap();
        assert_eq!(s, "B👋🌎".into());

        let mut s = Str::from("S👋🌎");
        s.set_substr(&2.into()..&2.into(), "B".into()).unwrap();
        assert_eq!(s, "S👋B".into());
    }

    #[test]
    fn test_arithmetic() {
        let result = Str::arithmetic_op(
            &Str::from("Hello, "),
            &Str::from("world!"),
            ArithmeticOperation::Add,
        )
        .unwrap();
        assert_eq!(result, Str::from("Hello, world!"));

        let result = Str::arithmetic_op(
            &Str::from("Hello, world!"),
            &Str::from("d!"),
            ArithmeticOperation::Subtract,
        )
        .unwrap();
        assert_eq!(result, Str::from("Hello, worl"));
    }

    #[test]
    fn test_boolean_logic() {
        let result = Str::boolean_op(
            &Str::from("Hello, "),
            &Str::from("world!"),
            BooleanOperation::And,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Str::boolean_op(
            &Str::from("Hello, "),
            &Str::from("world!"),
            BooleanOperation::Or,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Str::boolean_op(
            &Str::from("Hello, "),
            &Str::from("world!"),
            BooleanOperation::LT,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Str::boolean_op(
            &Str::from("Hello, "),
            &Str::from("world!"),
            BooleanOperation::GT,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result = Str::boolean_op(
            &Str::from("Hello, "),
            &Str::from("world!"),
            BooleanOperation::LTE,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Str::boolean_op(
            &Str::from("Hello, "),
            &Str::from("world!"),
            BooleanOperation::GTE,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result = Str::boolean_op(
            &Str::from("Hello, "),
            &Str::from("world!"),
            BooleanOperation::EQ,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result = Str::boolean_op(
            &Str::from("Hello, "),
            &Str::from("world!"),
            BooleanOperation::NEQ,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());
    }
}
