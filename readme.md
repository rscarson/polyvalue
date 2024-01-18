# Polyvalue
Single concrete type for representing values of different types

Built for [lavendeux-parser](https://github.com/rscarson/lavendeux-parser)

## Types

Values Can be bool, int, float, fixed, currency, string, array, object, or range.

All types implement Hash, Ord, Eq, Serialize, Deserialize, Clone, Debug and Default

Values of different types will be coerced to the same type when performing operations on them.

This is done using the following order-of-precedence:
- If either type is an object, the other type is coerced to an object. This is done by first converting the a type `T` to an array `[T]`, and then converting the array to an object of the form `{0: T}`.
- If either type is an array, the other type is coerced to an array.
- If either type is a string, the other type is coerced to a string.

At this point, remaining types are numeric and will be coerced to the type containing the most information. The order-of-precedence is:
- Currency
- Fixed
- Float
- Int
- Bool

## Operations

Operations can be performed directly on Value, or on inner types. Operations on Value will coerce the inner types to the same type, and then perform the operation.

There are 5 types of operations: arithmetic, bitwise, boolean, comparison, and indexing.

### Bitwise ops
- Bitwise not will attempt to remove the effect of the containing type's width, to remove trailing 0xF's 
- Negative RHS shifts will result in shifting in the oposite direction(eg; `1>>-1 == 1<<1`), and values >64 wrap using r%64
## Usage
```rust
use polyvalue::{Value, Int, Float, Fixed, Currency, Str, Array, Object, Range};

fn main() {
    let v = Value::from(1);
    assert_eq!(v, Value::Int(Int::new(1)));

    let v = Value::from(1.0).arithmetic_op(&Value::from(2.0), ArithmeticOperation::Add).unwrap();
    assert_eq!(v, Value::Float(Float::new(3.0)));
}
```

This crate was built for use in a parser, where the type of a value is not known until runtime.
Please open an issue if you have any suggestions for improvement.