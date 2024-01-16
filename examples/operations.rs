//! # Operations
//! Operations can be performed directly on Value, or on inner types. Operations on Value will
//! coerce the inner types to the same type, and then perform the operation.
//! 
//! There are 5 types of operations: arithmetic, bitwise, boolean, comparison, and indexing.
//! The first 3 are demonstrated below.
//! 
use polyvalue::{operations::*, Value};

fn main() {
    let value1 = Value::from(42);

    // When operation on a pair of values of different types, the opeerands are coerced to the
    // same type. In this case, the integer is coerced to a float.
    let value2 = Value::from(43.2);
    assert_eq!(
        Value::arithmetic_op(&value1, &value2, ArithmeticOperation::Add).unwrap(),
        Value::from(85.2)
    );

    // The same principle applies to non-numeric types. In this case, the integer is coerced to a
    // string, and the the subtraction operation will remove the string representation of the
    // integer from the string.
    let string_value = Value::from("Hello 42");
    assert_eq!(
        Value::arithmetic_op(&string_value, &value1, ArithmeticOperation::Subtract).unwrap(),
        Value::from("Hello ")
    );

    // There are also bitwise operations, which will always coerce to integers.
    let value1 = Value::from(0b1010);
    let value2 = Value::from(0b1100);
    assert_eq!(
        Value::bitwise_op(&value1, &value2, BitwiseOperation::And).unwrap(),
        Value::from(0b1000)
    );

    // And boolean operations, which will always coerce to booleans.
    let value1 = Value::from(42);
    let value2 = Value::from(false);
    assert_eq!(
        Value::boolean_op(&value1, &value2, BooleanOperation::And).unwrap(),
        Value::from(false)
    );
}
