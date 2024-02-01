//! Sized integer types
//!
//! These types represents integers of specific sizes.
//!
//! Like all subtypes, They are hashable, serializable, and fully comparable
//! They are represented as a string in the form of `<value>`
//!
use std::str::FromStr;

use crate::{operations::*, types::*, Error, Value, ValueTrait, ValueType};
use serde::{Deserialize, Serialize};

#[macro_use]
mod macros {
    macro_rules! sized_int_type {
        ($name:ident, $subtype:ident, $doc:literal) => {
            #[derive(
                PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default,
            )]
            /// A subtype of `Value` that represents a specific integer variant
            /// ranging from 8 to 64 bits, signed or unsigned
            #[doc = $doc]
            pub struct $name($subtype);
            impl_value!(
                $name,
                $subtype,
                |v: &Self| v.inner().to_string(),
                |v: &Self, f: &mut std::fmt::Formatter<'_>| {
                    write!(f, "{}{}", v.inner(), stringify!($subtype))
                }
            );

            impl $name {
                /// Bitwise NOT that attempts to remove the effect of the size of the integer:
                /// `!1u8 == 0u8` instead of `!1u8 == 254u8`
                pub fn unsized_bitwise_not(&self) -> Self {
                    let left = *self.inner();
                    if left == 0 {
                        (1).into()
                    } else {
                        let mask = ((0 as $subtype).wrapping_sub(1) as u64 >> left.leading_zeros())
                            as <Self as ValueTrait>::Inner;
                        (left ^ mask).into()
                    }
                }

                /// Creates a new integer from a string representation of a base-n number
                /// The string must be in the form of `0b<binary>`, `0o<octal>`, `0x<hex>`, or `0<octal>`
                /// ```
                pub fn from_str_radix(s: &str) -> Result<Self, Error> {
                    if s.len() < 2 {
                        return Err(Error::ValueConversion {
                            src_type: ValueType::String,
                            dst_type: ValueType::Int,
                        });
                    }

                    let mut s = s.trim().to_lowercase();
                    if s.remove(0) != '0' {
                        return Err(Error::ValueConversion {
                            src_type: ValueType::String,
                            dst_type: ValueType::Int,
                        });
                    }

                    let prefix = s.remove(0);
                    let radix = match prefix {
                        'b' => 2,
                        'o' => 8,
                        '0'..='7' => {
                            s.insert(0, prefix);
                            8
                        }
                        'x' => 16,
                        _ => {
                            return Err(Error::ValueConversion {
                                src_type: ValueType::String,
                                dst_type: ValueType::Int,
                            })
                        }
                    };

                    let value = $subtype::from_str_radix(&s, radix).map_err(|_| {
                        Error::ValueConversion {
                            src_type: ValueType::String,
                            dst_type: ValueType::Int,
                        }
                    })?;

                    if value > <$subtype>::MAX || value < <$subtype>::MIN {
                        return Err(Error::Overflow);
                    }
                    Ok($name::new(value as $subtype))
                }
            }
            map_value!(
                from = $name,
                handle_into = Value::$name,
                handle_from = |v: Value| match v {
                    Value::Range(_) => Self::try_from(v.as_a::<Array>()?),

                    Value::U8(v) => {
                        let v = *v.inner() as u8;
                        $subtype::try_from(v)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }

                    Value::U16(v) => {
                        let v = *v.inner() as u16;
                        $subtype::try_from(v)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }

                    Value::U32(v) => {
                        let v = *v.inner() as u32;
                        $subtype::try_from(v)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }

                    Value::U64(v) => {
                        let v = *v.inner() as u64;
                        $subtype::try_from(v)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }

                    Value::I8(v) => {
                        let v = *v.inner() as i8;
                        $subtype::try_from(v)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }

                    Value::I16(v) => {
                        let v = *v.inner() as i16;
                        $subtype::try_from(v)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }

                    Value::I32(v) => {
                        let v = *v.inner() as i32;
                        $subtype::try_from(v)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }

                    Value::I64(v) => {
                        let v = *v.inner();
                        $subtype::try_from(v)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }

                    Value::Fixed(v) => {
                        let p = v.inner().trunc().coefficient();
                        $subtype::try_from(p)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }
                    Value::Float(v) => {
                        let p = *v.inner();
                        let p = p.trunc() as i64;
                        $subtype::try_from(p)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }
                    Value::Currency(v) => {
                        let p = v.inner().value().inner().trunc().coefficient();
                        $subtype::try_from(p)
                            .map_err(|_| Error::Overflow)
                            .and_then(|v| Ok($name::new(v)))
                    }
                    Value::Bool(v) => {
                        let p = *v.inner() as i64;
                        Ok($name::new(p as $subtype))
                    }
                    Value::String(_) => {
                        Err(Error::ValueConversion {
                            src_type: ValueType::String,
                            dst_type: ValueType::$name,
                        })
                    }
                    Value::Array(v) => {
                        if v.inner().len() == 1 {
                            let v = v.inner()[0].clone();
                            $name::try_from(v)
                        } else {
                            Err(Error::ValueConversion {
                                src_type: ValueType::Array,
                                dst_type: ValueType::$name,
                            })
                        }
                    }
                    Value::Object(v) => {
                        if v.inner().len() == 1 {
                            let v = v.inner().values().next().unwrap().clone();
                            $name::try_from(v)
                        } else {
                            Err(Error::ValueConversion {
                                src_type: ValueType::Object,
                                dst_type: ValueType::$name,
                            })
                        }
                    }
                }
            );

            impl FromStr for $name {
                type Err = Error;

                fn from_str(s: &str) -> Result<Self, Self::Err> {
                    Ok($name::new(s.replace(',', "").parse::<$subtype>()?))
                }
            }

            map_type!(Array, $name);
            map_type!(Bool, $name);
            map_type!(Fixed, $name);
            map_type!(Float, $name);
            map_type!(Currency, $name);
            map_type!(Str, $name);
            map_type!(Object, $name);
            map_type!(Range, $name);

            overload_operator!($name, arithmetic);
            overload_operator!($name, bitwise);
            overload_operator!($name, deref);

            #[allow(unused_comparisons)]
            impl ArithmeticOperationExt for $name {
                fn arithmetic_op(
                    left: &Self,
                    right: &Self,
                    operation: ArithmeticOperation,
                ) -> Result<Self, crate::Error> {
                    let left = *left.inner();
                    let right = *right.inner();

                    let result = match operation {
                        ArithmeticOperation::Add => left.checked_add(right),
                        ArithmeticOperation::Subtract => left.checked_sub(right),
                        ArithmeticOperation::Multiply => left.checked_mul(right),
                        ArithmeticOperation::Divide => left.checked_div(right),
                        ArithmeticOperation::Modulo => left.checked_rem(right),
                        ArithmeticOperation::Exponentiate => {
                            if let Ok(right) = right.try_into() {
                                left.checked_pow(right)
                            } else {
                                None
                            }
                        }
                        ArithmeticOperation::Negate => {
                            if $subtype::MIN < 0 {
                                Some(-(left as i64) as $subtype)
                            } else {
                                return Err(Error::UnsupportedOperation {
                                    operation: operation.to_string(),
                                    actual_type: ValueType::$name,
                                });
                            }
                        }
                    }
                    .ok_or(Error::Overflow)?;
                    Ok(Self::new(result))
                }

                fn arithmetic_neg(&self) -> Result<Self, crate::Error>
                where
                    Self: Sized,
                {
                    Self::arithmetic_op(self, &self.clone(), ArithmeticOperation::Negate)
                }

                fn is_operator_supported(
                    &self,
                    _other: &Self,
                    operation: ArithmeticOperation,
                ) -> bool {
                    match operation {
                        ArithmeticOperation::Add
                        | ArithmeticOperation::Subtract
                        | ArithmeticOperation::Multiply
                        | ArithmeticOperation::Divide
                        | ArithmeticOperation::Modulo
                        | ArithmeticOperation::Exponentiate => true,
                        ArithmeticOperation::Negate => $subtype::MIN < 0,
                    }
                }
            }

            impl BooleanOperationExt for $name {
                fn boolean_op(
                    left: &Self,
                    right: &Self,
                    operation: BooleanOperation,
                ) -> Result<Value, Error> {
                    let result = match operation {
                        BooleanOperation::And => *left.inner() != 0 && *right.inner() != 0,
                        BooleanOperation::Or => *left.inner() != 0 || *right.inner() != 0,

                        BooleanOperation::LT => *left.inner() < *right.inner(),
                        BooleanOperation::GT => *left.inner() > *right.inner(),
                        BooleanOperation::LTE => *left.inner() <= *right.inner(),
                        BooleanOperation::GTE => *left.inner() >= *right.inner(),
                        BooleanOperation::EQ => *left.inner() == *right.inner(),
                        BooleanOperation::NEQ => *left.inner() != *right.inner(),
                        BooleanOperation::Not => *left.inner() == 0,
                    };

                    Ok(result.into())
                }

                fn boolean_not(&self) -> Result<Value, crate::Error>
                where
                    Self: Sized,
                {
                    Self::boolean_op(self, &self.clone(), BooleanOperation::Not)
                }
            }

            #[allow(unused_comparisons)]
            impl BitwiseOperationExt for $name {
                fn bitwise_op(
                    left: &Self,
                    right: &Self,
                    operation: BitwiseOperation,
                ) -> Result<Self, Error> {
                    let operation = operation;
                    let left = *left.inner();
                    let right = *right.inner();

                    let result = match operation {
                        BitwiseOperation::And => Some(left & right),
                        BitwiseOperation::Or => Some(left | right),
                        BitwiseOperation::Xor => Some(left ^ right),

                        BitwiseOperation::LeftShift if right < 0 => {
                            left.checked_shr(-(right as i64) as u32)
                        }
                        BitwiseOperation::LeftShift => {
                            left.checked_shl((right % $subtype::BITS as $subtype) as u32)
                        }

                        BitwiseOperation::RightShift if right < 0 => {
                            left.checked_shl(-(right as i64) as u32)
                        }
                        BitwiseOperation::RightShift => {
                            left.checked_shr((right % $subtype::BITS as $subtype) as u32)
                        }
                        BitwiseOperation::Not => Some(!left),
                    }
                    .ok_or(Error::Overflow)?;

                    Ok(Self::new(result))
                }

                fn bitwise_not(&self) -> Result<Self, Error>
                where
                    Self: Sized,
                {
                    Self::bitwise_op(self, &self.clone(), BitwiseOperation::Not)
                }
            }
        };
    }
}

sized_int_type!(I8, i8, "8 bit signed integer");
sized_int_type!(I16, i16, "16 bit signed integer");
sized_int_type!(I32, i32, "32 bit signed integer");
sized_int_type!(I64, i64, "64 bit signed integer");
sized_int_type!(U8, u8, "8 bit unsigned integer");
sized_int_type!(U16, u16, "16 bit unsigned integer");
sized_int_type!(U32, u32, "32 bit unsigned integer");
sized_int_type!(U64, u64, "64 bit unsigned integer");

impl From<usize> for U64 {
    fn from(v: usize) -> Self {
        Self::new(v as u64)
    }
}

impl From<usize> for Value {
    fn from(v: usize) -> Self {
        Self::U64(v.into())
    }
}

// Let all types be built from the i32 primitive
impl From<i32> for U8 {
    fn from(v: i32) -> Self {
        Self::new(v as u8)
    }
}
impl From<i32> for U16 {
    fn from(v: i32) -> Self {
        Self::new(v as u16)
    }
}
impl From<i32> for U32 {
    fn from(v: i32) -> Self {
        Self::new(v as u32)
    }
}
impl From<i32> for U64 {
    fn from(v: i32) -> Self {
        Self::new(v as u64)
    }
}
impl From<i32> for I8 {
    fn from(v: i32) -> Self {
        Self::new(v as i8)
    }
}
impl From<i32> for I16 {
    fn from(v: i32) -> Self {
        Self::new(v as i16)
    }
}
impl From<i32> for I64 {
    fn from(v: i32) -> Self {
        Self::new(v as i64)
    }
}

// Now we map all subtypes to all other subtypes
map_type!(I8, U8);
map_type!(I8, U16);
map_type!(I8, U32);
map_type!(I8, U64);
map_type!(I8, I16);
map_type!(I8, I32);
map_type!(I8, I64);

map_type!(I16, U8);
map_type!(I16, U16);
map_type!(I16, U32);
map_type!(I16, U64);
map_type!(I16, I8);
map_type!(I16, I32);
map_type!(I16, I64);

map_type!(I32, U8);
map_type!(I32, U16);
map_type!(I32, U32);
map_type!(I32, U64);
map_type!(I32, I8);
map_type!(I32, I16);
map_type!(I32, I64);

map_type!(I64, U8);
map_type!(I64, U16);
map_type!(I64, U32);
map_type!(I64, U64);
map_type!(I64, I8);
map_type!(I64, I16);
map_type!(I64, I32);

map_type!(U8, I8);
map_type!(U8, I16);
map_type!(U8, I32);
map_type!(U8, I64);
map_type!(U8, U16);
map_type!(U8, U32);
map_type!(U8, U64);

map_type!(U16, I8);
map_type!(U16, I16);
map_type!(U16, I32);
map_type!(U16, I64);
map_type!(U16, U8);
map_type!(U16, U32);
map_type!(U16, U64);

map_type!(U32, I8);
map_type!(U32, I16);
map_type!(U32, I32);
map_type!(U32, I64);
map_type!(U32, U8);
map_type!(U32, U16);
map_type!(U32, U64);

map_type!(U64, I8);
map_type!(U64, I16);
map_type!(U64, I32);
map_type!(U64, I64);
map_type!(U64, U8);
map_type!(U64, U16);
map_type!(U64, U32);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_unsized_bitwise_not() {
        assert_eq!(U8::new(0).unsized_bitwise_not(), U8::new(1));
        assert_eq!(U8::new(1).unsized_bitwise_not(), U8::new(0));
        assert_eq!(U16::new(0xF0).unsized_bitwise_not(), U16::new(0x0F));
        assert_eq!(I64::new(0xF0).unsized_bitwise_not(), I64::new(0x0F));
    }

    #[test]
    fn test_boolean() {
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(5), BooleanOperation::And).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(5), BooleanOperation::Or).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(5), BooleanOperation::LT).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(5), BooleanOperation::GT).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(5), BooleanOperation::LTE).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(5), BooleanOperation::GTE).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(5), BooleanOperation::EQ).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(5), BooleanOperation::NEQ).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(5), BooleanOperation::Not).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(0), &I8::new(5), BooleanOperation::Not).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(10), &I8::new(0), BooleanOperation::Not).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            I8::boolean_op(&I8::new(0), &I8::new(0), BooleanOperation::Not).unwrap(),
            Value::from(true)
        );
        assert_eq!(I8::boolean_not(&I8::new(10)).unwrap(), Value::from(false));
    }

    #[test]
    fn test_bitwise() {
        assert_eq!(
            I8::bitwise_op(&I8::new(10), &I8::new(5), BitwiseOperation::And).unwrap(),
            I8::new(0)
        );
        assert_eq!(
            I8::bitwise_op(&I8::new(10), &I8::new(5), BitwiseOperation::Or).unwrap(),
            I8::new(15)
        );
        assert_eq!(
            I8::bitwise_op(&I8::new(10), &I8::new(5), BitwiseOperation::Xor).unwrap(),
            I8::new(15)
        );
        assert_eq!(
            I8::bitwise_op(&I8::new(10), &I8::new(1), BitwiseOperation::LeftShift).unwrap(),
            I8::new(20)
        );
        assert_eq!(
            I8::bitwise_op(&I8::new(10), &I8::new(5), BitwiseOperation::RightShift).unwrap(),
            I8::new(0)
        );
        assert_eq!(
            I8::bitwise_op(&I8::new(10), &I8::new(-5), BitwiseOperation::LeftShift).unwrap(),
            I8::new(0)
        );
        assert_eq!(
            I8::bitwise_op(&I8::new(10), &I8::new(-1), BitwiseOperation::RightShift).unwrap(),
            I8::new(20)
        );
        assert_eq!(
            I8::bitwise_op(&I8::new(10), &I8::new(10), BitwiseOperation::Not).unwrap(),
            I8::new(-11)
        );
        assert_eq!(
            I8::bitwise_op(&I8::new(10), &I8::new(-5), BitwiseOperation::Not).unwrap(),
            I8::new(-11)
        );
        assert_eq!(
            I8::bitwise_op(&I8::new(-10), &I8::new(5), BitwiseOperation::Not).unwrap(),
            I8::new(9)
        );
        assert_eq!(I8::bitwise_not(&I8::new(-10)).unwrap(), I8::new(9));
    }

    #[test]
    fn test_arithmetic() {
        assert_eq!(
            I8::arithmetic_op(&I8::new(10), &I8::new(5), ArithmeticOperation::Add).unwrap(),
            I8::new(15)
        );
        assert_eq!(
            I8::arithmetic_op(&I8::new(10), &I8::new(5), ArithmeticOperation::Subtract).unwrap(),
            I8::new(5)
        );
        assert_eq!(
            I8::arithmetic_op(&I8::new(10), &I8::new(5), ArithmeticOperation::Multiply).unwrap(),
            I8::new(50)
        );
        assert_eq!(
            I8::arithmetic_op(&I8::new(10), &I8::new(5), ArithmeticOperation::Divide).unwrap(),
            I8::new(2)
        );
        assert_eq!(
            I8::arithmetic_op(&I8::new(10), &I8::new(5), ArithmeticOperation::Modulo).unwrap(),
            I8::new(0)
        );
        I8::arithmetic_op(&I8::new(10), &I8::new(5), ArithmeticOperation::Exponentiate)
            .unwrap_err();
        I64::arithmetic_op(
            &I64::new(10),
            &I64::new(i64::MAX),
            ArithmeticOperation::Exponentiate,
        )
        .unwrap_err();

        U8::arithmetic_neg(&U8::new(10)).unwrap_err();
        assert_eq!(I8::arithmetic_neg(&I8::new(10)).unwrap(), I8::new(-10));

        let i = I8::new(10);
        let u = U8::new(10);
        assert!(
            U8::is_operator_supported(&u, &u, ArithmeticOperation::Add)
        );
        assert!(
            !U8::is_operator_supported(&u, &u, ArithmeticOperation::Negate)
        );
        assert!(
            I8::is_operator_supported(&i, &i, ArithmeticOperation::Negate)
        );
    }

    #[test]
    fn test_from_str() {
        assert_eq!(I8::from_str_radix("0b1010").unwrap(), I8::new(10));
        I8::from_str_radix("0b10000000000000").unwrap_err();

        assert_eq!(I16::from_str_radix("0b1010").unwrap(), I16::new(10));
        I16::from_str_radix("0b10000000000000000").unwrap_err();

        assert_eq!(I32::from_str_radix("0b1010").unwrap(), I32::new(10));
        assert_eq!(I32::from_str_radix("0b1").unwrap(), I32::new(1));

        assert_eq!(I64::from_str_radix("0b1010").unwrap(), I64::new(10));
        assert_eq!(I64::from_str_radix("0b11111").unwrap(), I64::new(31));

        assert_eq!(U8::from_str_radix("0b1010").unwrap(), U8::new(10));
        U8::from_str_radix("0b10000000000000").unwrap_err();

        assert_eq!(U16::from_str_radix("0b1010").unwrap(), U16::new(10));
        U16::from_str_radix("0b10000000000000000").unwrap_err();

        assert_eq!(U32::from_str_radix("0b1010").unwrap(), U32::new(10));
        assert_eq!(U32::from_str_radix("0b1").unwrap(), U32::new(1));

        assert_eq!(U64::from_str_radix("0b1010").unwrap(), U64::new(10));
        assert_eq!(U64::from_str_radix("0b11111").unwrap(), U64::new(31));
        assert_eq!(U64::from_str_radix("0xFF").unwrap(), U64::new(255));
        assert_eq!(U64::from_str_radix("0o7").unwrap(), U64::new(7));
        assert_eq!(U64::from_str_radix("07").unwrap(), U64::new(7));

        I8::from_str_radix("0").unwrap_err();
        I8::from_str_radix("0o").unwrap_err();
        I8::from_str_radix("1x1").unwrap_err();
        I8::from_str_radix("0n1").unwrap_err();
        I8::from_str_radix("0xFFF").unwrap_err();

        let mut u = U64::from_str_radix("0b11111").unwrap();
        *u.inner_mut() = 32;
        assert_eq!(u, U64::new(32));

        assert_eq!(I8::from_str("10").unwrap(), I8::new(10));
        assert_eq!(I16::from_str("10,000").unwrap(), I16::new(10000));
        I8::from_str("10,000").unwrap_err();
    }

    #[test]
    fn test_to_string() {
        assert_eq!(I8::new(10).to_string(), "10");
        assert_eq!(I16::new(10).to_string(), "10");
        assert_eq!(I32::new(10).to_string(), "10");
        assert_eq!(I64::new(10).to_string(), "10");
        assert_eq!(U8::new(10).to_string(), "10");
        assert_eq!(U16::new(10).to_string(), "10");
        assert_eq!(U32::new(10).to_string(), "10");
        assert_eq!(U64::new(10).to_string(), "10");
    }
}
