//! # Type Cooersion
//! Values of different types will be coerced to the same type when performing operations on them.
//! This is done using the following order-of-precedence:
//! - If either type is an object, the other type is coerced to an object.
//!   This is done by first converting the a type `T` to an array `[T]`, and then converting the
//!   array to an object of the form `{0: T}`.
//! - If either type is an array, the other type is coerced to an array.
//! - If either type is a string, the other type is coerced to a string.
//!
//! At this point, remaining types are numeric and will be coerced to the type containing the
//! most information. The order-of-precedence is:
//! - Currency
//! - Fixed
//! - Float
//! - Int
//! - Bool
//!
//! Please note that this priority system is also used when ordering a list of values.
//!
use polyvalue::{types::*, Value};
use std::str::FromStr;

fn main() {
    // In this sample, the currency value $50.000 is higher priority than the int value 1
    // Therefore, the int value is coerced to a compatible currency value with a value of
    // $1.000
    let (left, right) = Value::from(1)
        .resolve(Value::from(CurrencyInner::from_str("$50.000").unwrap()))
        .unwrap();
    assert_eq!(
        left,
        Value::from(CurrencyInner::from_str("$1.000").unwrap())
    );
    assert_eq!(
        right,
        Value::from(CurrencyInner::from_str("$50.000").unwrap())
    );

    // Here, the string value is higher priority, so both values are coerced to strings
    let (left, right) = Value::from("hello world")
        .resolve(Value::from(false))
        .unwrap();
    assert_eq!(left, Value::from("hello world"));
    assert_eq!(right, Value::from("false"));

    // Here the integer value is cooerced to an array
    let (_, right) = Value::from(vec![Value::from(1), Value::from(2)])
        .resolve(Value::from(3))
        .unwrap();
    assert_eq!(right, Value::from(vec![Value::from(3)]));
}
