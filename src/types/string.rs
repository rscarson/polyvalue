//! String type
//!
//! This type is a wrapper around `String`
//!
//! Like all subtypes, it is hashable, serializable, and fully comparable
//! It is represented as a string in the form of `<value>`
//!
use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};
use std::ops::{Range, RangeInclusive};

/// Subtype of `Value` that represents a string
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default)]
pub struct Str(String);
impl_value!(
    Str,
    String,
    |v: &Self| v.inner().clone(),
    |v: &Self, f: &mut std::fmt::Formatter<'_>| { write!(f, "'{}'", v.inner()) }
);

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

impl Str {
    /// Maps a range of values to a range of bytes in a string coresponding to the same characters
    /// This is necessary because the string is UTF-8 encoded
    /// Can fail if the range is out of bounds, or if the range is not a valid integer range
    fn map_range_to_bytes(&self, range: RangeInclusive<&Value>) -> Result<Range<usize>, Error> {
        let mut range = *I64::try_from((*range.start()).clone())?.inner()
            ..*I64::try_from((*range.end()).clone())?.inner();

        let chars = self.inner().chars().count() as i64;
        if range.start < 0 {
            range.start += chars;
        }
        if range.end < 0 {
            range.end += chars;
        }
        let mut range = range.start as usize..range.end as usize;

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
    pub fn substr(&self, index: RangeInclusive<&Value>) -> Result<&str, crate::Error> {
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
    pub fn mut_substr(&mut self, index: RangeInclusive<&Value>) -> Result<&mut str, crate::Error> {
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
    pub fn set_substr(
        &mut self,
        index: RangeInclusive<&Value>,
        value: Value,
    ) -> Result<(), crate::Error> {
        let range = *I64::try_from((*index.start()).clone())?.inner() as usize
            ..*I64::try_from((*index.end()).clone())?.inner() as usize;

        let value = Str::try_from(value)?.inner().clone();

        let prefix = if range.start == 0 {
            "".to_string()
        } else {
            self.substr(&0.into()..=&(range.start - 1).into())?
                .to_string()
        };

        let char_count = self.inner_mut().chars().count();
        let suffix = if range.end == char_count - 1 {
            ""
        } else {
            self.substr(&(range.end + 1).into()..=&(char_count - 1).into())?
        };

        *self.inner_mut() = format!("{}{}{}", prefix, value, suffix);
        Ok(())
    }

    /// Convert an index value to a range, useful for bridging the gap between
    /// the IndexingOperationExt trait and the substr functions
    /// Can fail if the index is not an array of integers, or if the array is empty
    pub fn index_value_to_range(index: &Value) -> Result<std::ops::RangeInclusive<Value>, Error> {
        // Convert index to a range - we will need an array of integers
        let index = index.as_a::<Array>()?;
        let indices = index
            .inner()
            .iter()
            .map(|v| Ok::<<I64 as ValueTrait>::Inner, Error>(*v.as_a::<I64>()?.inner()))
            .collect::<Result<Vec<_>, _>>()?;
        if indices.is_empty() {
            Err(Error::Index {
                key: index.to_string(),
            })?;
        }

        let start = Value::from(*indices.iter().min().unwrap());
        let end = Value::from(*indices.iter().max().unwrap());
        Ok(start..=end)
    }
}

map_value!(
    from = Str,
    handle_into = Value::String,
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

overload_operator!(Str, add);
overload_operator!(Str, sub);
overload_operator!(Str, neg);
overload_operator!(Str, deref);

impl MatchingOperationExt for Str {
    fn matching_op(
        container: &Self,
        pattern: &Value,
        operation: MatchingOperation,
    ) -> Result<Value, crate::Error>
    where
        Self: Sized,
    {
        let pattern = Str::try_from(pattern.clone())?;
        let result = match operation {
            MatchingOperation::Contains => {
                let pattern = pattern.inner().as_str();
                let pattern = convert_regex_string(pattern, |s: String| s)?;
                pattern.is_match(container.inner().as_str())
            }
            MatchingOperation::StartsWith => {
                container.inner().starts_with(pattern.inner().as_str())
            }
            MatchingOperation::EndsWith => container.inner().ends_with(pattern.inner().as_str()),
            MatchingOperation::Matches => {
                let pattern = pattern.inner().as_str();
                let pattern = convert_regex_string(pattern, |mut s: String| {
                    if !s.starts_with('^') {
                        s = "^".to_string() + s.as_str();
                    }
                    if !s.ends_with('$') {
                        s += "$"
                    }
                    s
                })?;
                pattern.is_match(container.inner().as_str())
            }

            // Handled by Value
            _ => false,
        };

        Ok(result.into())
    }
}

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

            // reverse string
            ArithmeticOperation::Negate => {
                let mut result = left.clone();
                result = result.chars().rev().collect();
                result
            }

            _ => Err(Error::UnsupportedOperation {
                operation: operation.to_string(),
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

    fn is_operator_supported(&self, _: &Self, operation: ArithmeticOperation) -> bool {
        match operation {
            ArithmeticOperation::Add
            | ArithmeticOperation::Subtract
            | ArithmeticOperation::Negate => true,
            _ => false,
        }
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

impl IndexingOperationExt for Str {
    fn get_index(&self, index: &Value) -> Result<Value, crate::Error> {
        self.substr(index..=index).and_then(|s| Ok(Value::from(s)))
    }

    fn get_indices(&self, index: &Value) -> Result<Value, crate::Error> {
        if index.is_a(ValueType::Range) {
            let indices = index.as_a::<crate::types::Range>()?.inner().clone();
            let lower = Value::from(*indices.start());
            let upper = Value::from(*indices.end());
            self.substr(&lower..=&upper)
                .and_then(|s| Ok(Value::from(s)))
        } else {
            let indices = index.as_a::<Array>()?;
            if indices.inner().is_empty() {
                return Ok(Value::from(""));
            }

            let results = indices
                .inner()
                .iter()
                .map(|i| Ok(self.get_index(i)?.as_a::<Str>()?.inner().to_string()))
                .collect::<Result<Vec<_>, Error>>()?;
            // join into one Str
            Ok(Value::from(results.join("")))
        }
    }
}

// This function will convert a string of either forms `/pattern/flags` or `pattern` to a regex object
fn convert_regex_string<F>(input: &str, formatting_callback: F) -> Result<regex::Regex, Error>
where
    F: Fn(String) -> String,
{
    let mut pattern = input.to_string();
    let mut flags = None;

    // Check if the string contains a regex pattern
    if input.starts_with('/') {
        let end = input.rfind('/').unwrap();
        if end != 0 {
            pattern = input[1..end].to_string();
            flags = Some(input[end + 1..].to_string());
        }
    }

    pattern = formatting_callback(pattern);

    let mut regex = regex::RegexBuilder::new(&pattern);
    if let Some(flags) = flags {
        for flag in flags.chars() {
            match flag {
                'i' => regex.case_insensitive(true),
                'm' => regex.multi_line(true),
                's' => regex.dot_matches_new_line(true),
                'U' => regex.swap_greed(true),
                'u' => regex.unicode(true),
                'x' => regex.ignore_whitespace(true),
                _ => {
                    return Err(Error::InvalidRegexFlag(flag.to_string()));
                }
            };
        }
    }

    Ok(regex.build()?)
}

//
// Tests
//

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_matching() {
        let result = Str::matching_op(
            &Str::from("Hello, world!"),
            &Str::from("[a-z]").into(),
            MatchingOperation::Contains,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Str::matching_op(
            &Str::from("Hello, world!"),
            &Str::from("world").into(),
            MatchingOperation::StartsWith,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        let result = Str::matching_op(
            &Str::from("Hello, world!"),
            &Str::from("world!").into(),
            MatchingOperation::EndsWith,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Str::matching_op(
            &Str::from("Hello, world!"),
            &Str::from("Hello, w..ld!").into(),
            MatchingOperation::Matches,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Str::matching_op(
            &Str::from("Hello, world!"),
            &Str::from("/h.*/i").into(),
            MatchingOperation::Matches,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        // test the m s U u x flags
        let result = Str::matching_op(
            &Str::from("Hello\n, world!"),
            &Str::from("/h.*/isUuxm").into(),
            MatchingOperation::Matches,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Str::matching_op(
            &Str::from("Hello, world!"),
            &Str::from("/H.*/").into(),
            MatchingOperation::Matches,
        )
        .unwrap();
        assert_eq!(result, Bool::from(true).into());

        let result = Str::matching_op(
            &Str::from("Hello, world!"),
            &Str::from("/h.*").into(),
            MatchingOperation::Matches,
        )
        .unwrap();
        assert_eq!(result, Bool::from(false).into());

        Str::matching_op(
            &Str::from("Hello, world!"),
            &Str::from("/h.*/y").into(),
            MatchingOperation::Matches,
        )
        .unwrap_err();
    }

    #[test]
    fn test_indexing() {
        let value_range = Array::from(vec![0.into(), 1.into(), 2.into()]);
        let value_range = Value::from(value_range);
        let value_range = Str::index_value_to_range(&value_range).unwrap();
        let value_range = value_range.start()..=value_range.end();
        assert_eq!(value_range.start(), &&Value::i64(0));
        assert_eq!(value_range.end(), &&Value::i64(2));
        let s = Str::from("012");
        assert_eq!(s.substr(value_range).unwrap(), "012");

        // test mut_substr
        let mut s = Str::from("012");
        assert_eq!(s.mut_substr(&0.into()..=&1.into()).unwrap(), "01");

        let s = Str::from("012");
        assert_eq!(s.substr(&(-2).into()..=&(-1).into()).unwrap(), "12");

        // normal string
        let s = Str::from("Hello, world!");
        assert_eq!(s.substr(&0.into()..=&1.into()).unwrap(), "He");

        // Bad and scary unicode string, with multibyte chars at the start
        let s = Str::from("👋🌎");
        assert_eq!(s.substr(&0.into()..=&0.into()).unwrap(), "👋");

        let mut s = Str::from("S👋🌎");
        s.set_substr(&1.into()..=&1.into(), "B".into()).unwrap();
        assert_eq!(s, "SB🌎".into());

        let mut s = Str::from("S👋🌎");
        s.set_substr(&0.into()..=&1.into(), "B".into()).unwrap();
        assert_eq!(s, "B🌎".into());

        let mut s = Str::from("S👋🌎");
        s.set_substr(&0.into()..=&0.into(), "B".into()).unwrap();
        assert_eq!(s, "B👋🌎".into());

        let mut s = Str::from("S👋🌎");
        s.set_substr(&2.into()..=&2.into(), "B".into()).unwrap();
        assert_eq!(s, "S👋B".into());

        let s = Str::from("S👋🌎");
        let s = s
            .get_indices(&Value::from(vec![0.into(), 2.into()]))
            .unwrap();
        assert_eq!(s, "S🌎".into());

        let s = Str::from("S👋🌎");
        let s = s.get_indices(&Value::from(vec![])).unwrap();
        assert_eq!(s, "".into());

        let s = Str::from("S👋🌎");
        let s = s.get_indices(&Value::from(0..=1)).unwrap();
        assert_eq!(s, "S👋".into());
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

        let result = Str::arithmetic_neg(&Str::from("Hello, world!")).unwrap();
        assert_eq!(result, Str::from("!dlrow ,olleH"));

        // now with emojis
        let result = Str::arithmetic_neg(&Str::from("👋🌎")).unwrap();
        assert_eq!(result, Str::from("🌎👋"));

        Str::arithmetic_op(
            &Str::from("👋🌎"),
            &Str::from("🌎"),
            ArithmeticOperation::Divide,
        )
        .unwrap_err();

        assert_eq!(
            true,
            Str::is_operator_supported(
                &Str::from("Hello, world!"),
                &Str::from("d!"),
                ArithmeticOperation::Subtract
            )
        );
        assert_eq!(
            false,
            Str::is_operator_supported(
                &Str::from("Hello, world!"),
                &Str::from("d!"),
                ArithmeticOperation::Divide
            )
        );
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

        let result = Str::boolean_not(&Str::from("Hello, world!")).unwrap();
        assert_eq!(result, Bool::from(false).into());
    }
}
