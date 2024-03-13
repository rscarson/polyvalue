//! Sized integer types
//!
//! These types represents integers of specific sizes.
//!
//! Like all subtypes, They are hashable, serializable, and fully comparable
//! They are represented as a string in the form of `<value>`
//!
use std::str::FromStr;

use crate::{operations::*, types::*, Error, InnerValue, Value, ValueTrait, ValueType};
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
                |v: &Self| { v.inner().to_string() },
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

                /// Shift that always ignores the msb
                pub fn logical_lshift(&self, right: i32) -> Result<Self, Error> {
                    let left = *self.inner();
                    let right = if right < 0 {
                        return self.logical_rshift(-right);
                    } else {
                        right as u32
                    };

                    // Get the bit adjacent to the msb
                    let mask = 1 << ($subtype::BITS - 2);
                    let new_msb = (left & mask) << 1;

                    // Shift as usual, then place the new msb
                    let result = left.checked_shl(right).ok_or(Error::Overflow)?;
                    Ok(Self::new(result | new_msb))
                }

                /// Shift that always ignores the msb
                pub fn logical_rshift(&self, right: i32) -> Result<Self, Error> {
                    let left = *self.inner();
                    let right = if right < 0 {
                        return self.logical_lshift(-right);
                    } else {
                        right as u32
                    };

                    // mask off the msb of left
                    let mask = 1 << ($subtype::BITS - 1);
                    let has_msb = left & mask == mask;

                    // now shift the version with a cleared msb
                    let result = (left & !mask).checked_shr(right).ok_or(Error::Overflow)?;

                    // if the msb was set, set it back, one bit to the right
                    Ok(Self::new(if has_msb {
                        result | (mask >> 1) & !mask
                    } else {
                        result & !mask
                    }))
                }

                /// Shift that always preserves the msb
                pub fn arithmetic_lshift(&self, right: i32) -> Result<Self, Error> {
                    let left = *self.inner();
                    let right = if right < 0 {
                        return self.arithmetic_rshift(-right);
                    } else {
                        right as u32
                    };

                    // mask off the msb of left
                    let mask = 1 << ($subtype::BITS - 1);
                    let has_msb = (left & mask) == mask;

                    // Shift as usual, then replace the msb
                    let result = left.checked_shl(right).ok_or(Error::Overflow)?;

                    if has_msb {
                        Ok(Self::new(result | mask))
                    } else {
                        Ok(Self::new(result & !mask))
                    }
                }

                /// Shift that always preserves the msb
                pub fn arithmetic_rshift(&self, right: i32) -> Result<Self, Error> {
                    let left = *self.inner();
                    let right = if right < 0 {
                        return self.arithmetic_lshift(-right);
                    } else {
                        right as u32
                    };

                    // mask off the msb of left
                    let mask = 1 << ($subtype::BITS - 1);
                    let has_msb = (left & mask) == mask;

                    // Shift as usual, zero adjascent bit, then replace the msb
                    let result = left.checked_shr(right).ok_or(Error::Overflow)?;
                    let result = result & !(mask >> 1);

                    if has_msb {
                        Ok(Self::new(result | mask))
                    } else {
                        Ok(Self::new(result))
                    }
                }

                /// Creates a new integer from a string representation of a base-n number
                /// The string must be in the form of `0b<binary>`, `0o<octal>`, `0x<hex>`, or `0<octal>`
                /// ```
                #[allow(unused_comparisons)]
                pub fn from_str_radix(s: &str) -> Result<Self, Error> {
                    let mut s = s.trim().chars().into_iter().peekable();
                    match s.peek() {
                        // Base n
                        Some('0') => {
                            s.next();
                            let mut should_advance = true;
                            let base = match s.peek() {
                                Some('b') => 2,
                                Some('o') => 8,
                                Some('x') => 16,
                                Some(_) => {
                                    should_advance = false;
                                    8
                                }
                                None => return Ok(Self::new(0)),
                            };
                            if should_advance {
                                s.next();
                            }
                            let remainder = s.collect::<String>().replace('_', "");
                            if remainder.is_empty() {
                                Ok(Self::new(0))
                            } else {
                                let large_ures = u64::from_str_radix(&remainder, base)?;
                                if large_ures > $subtype::MAX as u64 && $subtype::MIN < 0 {
                                    let offset = (large_ures - $subtype::MAX as u64) - 1;
                                    if offset > $subtype::MAX as u64 {
                                        return Err(Error::Overflow);
                                    } else {
                                        Ok(Self::new($subtype::MIN + offset as $subtype))
                                    }
                                } else if large_ures <= $subtype::MAX as u64 {
                                    Ok(Self::new(large_ures as $subtype))
                                } else {
                                    Err(Error::Overflow)
                                }
                            }
                        }

                        // Base 10
                        Some(_) => {
                            let s = s.collect::<String>().replace('_', "");
                            Ok(Self::new(s.parse::<$subtype>()?))
                        }

                        // Empty string
                        None => Ok(Self::new(0)),
                    }
                }
            }
            map_value!(
                from = $name,
                handle_into = (v) { Value::$subtype(v) },
                handle_from = (v) {
                    match v.inner() {
                        InnerValue::Range(_) => Self::try_from(v.as_a::<Array>()?),

                        InnerValue::U8(v) => {
                            let v = *v.inner() as u8;
                            $subtype::try_from(v)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }

                        InnerValue::U16(v) => {
                            let v = *v.inner() as u16;
                            $subtype::try_from(v)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }

                        InnerValue::U32(v) => {
                            let v = *v.inner() as u32;
                            $subtype::try_from(v)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }

                        InnerValue::U64(v) => {
                            let v = *v.inner() as u64;
                            $subtype::try_from(v)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }

                        InnerValue::I8(v) => {
                            let v = *v.inner() as i8;
                            $subtype::try_from(v)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }

                        InnerValue::I16(v) => {
                            let v = *v.inner() as i16;
                            $subtype::try_from(v)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }

                        InnerValue::I32(v) => {
                            let v = *v.inner() as i32;
                            $subtype::try_from(v)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }

                        InnerValue::I64(v) => {
                            let v = *v.inner();
                            $subtype::try_from(v)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }

                        InnerValue::Fixed(v) => {
                            let p = v.inner().trunc().coefficient();
                            $subtype::try_from(p)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }
                        InnerValue::Float(v) => {
                            let p = *v.inner();
                            let p = p.trunc() as i64;
                            $subtype::try_from(p)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }
                        InnerValue::Currency(v) => {
                            let p = v.inner().value().inner().trunc().coefficient();
                            $subtype::try_from(p)
                                .map_err(|_| Error::Overflow)
                                .and_then(|v| Ok($name::new(v)))
                        }
                        InnerValue::Bool(v) => {
                            let p = *v.inner() as i64;
                            Ok($name::new(p as $subtype))
                        }
                        InnerValue::String(_) => {
                            Err(Error::ValueConversion {
                                src_type: ValueType::String,
                                dst_type: ValueType::$name,
                            })
                        }
                        InnerValue::Array(v) => {
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
                        InnerValue::Object(v) => {
                            let len = v.inner().len();
                            match v.inner().values().next() {
                                Some(v) if len == 1 => {
                                    $name::try_from(v.clone())
                                }

                                _ => Err(Error::ValueConversion {
                                    src_type: ValueType::Object,
                                    dst_type: ValueType::$name,
                                }),
                            }
                        }
                    }
                }
            );

            impl FromStr for $name {
                type Err = Error;

                fn from_str(s: &str) -> Result<Self, Self::Err> {
                    Self::from_str_radix(s)
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
                    self,
                    right: Self,
                    operation: ArithmeticOperation,
                ) -> Result<Self, crate::Error> {
                    let left = self.into_inner();
                    let right = right.into_inner();

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
                    }
                    .ok_or(Error::Overflow)?;
                    Ok(Self::new(result))
                }

                fn arithmetic_neg(self) -> Result<Self, crate::Error>
                where
                    Self: Sized,
                {
                    if $subtype::MIN < 0 {
                        Ok(Self(-(self.into_inner() as i64) as $subtype))
                    } else {
                        return Err(Error::UnsupportedOperation {
                            operation: "negation".to_string(),
                            actual_type: ValueType::$name,
                        });
                    }
                }
            }

            impl BooleanOperationExt for $name {
                fn boolean_op(
                    self,
                    right: Self,
                    operation: BooleanOperation,
                ) -> Result<Value, Error> {
                    let left = self.into_inner();
                    let right = right.into_inner();

                    let result = match operation {
                        BooleanOperation::And => left != 0 && right != 0,
                        BooleanOperation::Or => left != 0 || right != 0,

                        BooleanOperation::LT => left < right,
                        BooleanOperation::GT => left > right,
                        BooleanOperation::LTE => left <= right,
                        BooleanOperation::GTE => left >= right,
                        BooleanOperation::EQ | BooleanOperation::StrictEQ => left == right,
                        BooleanOperation::NEQ | BooleanOperation::StrictNEQ => left != right,
                    };

                    Ok(result.into())
                }

                fn boolean_not(self) -> Result<Value, crate::Error>
                where
                    Self: Sized,
                {
                    Ok((self.into_inner() == 0).into())
                }
            }

            #[allow(unused_comparisons)]
            impl BitwiseOperationExt for $name {
                fn bitwise_op(
                    self,
                    right: Self,
                    operation: BitwiseOperation,
                ) -> Result<Self, Error> {
                    let left = self.into_inner();
                    let right = right.into_inner();

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
                    }
                    .ok_or(Error::Overflow)?;

                    Ok(Self::new(result))
                }

                fn bitwise_not(self) -> Result<Self, Error>
                where
                    Self: Sized,
                {
                    Ok(Self(!self.into_inner()))
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
        Self::u64(v)
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
            I8::boolean_op(I8::new(10), I8::new(5), BooleanOperation::And).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(I8::new(10), I8::new(5), BooleanOperation::Or).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(I8::new(10), I8::new(5), BooleanOperation::LT).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            I8::boolean_op(I8::new(10), I8::new(5), BooleanOperation::GT).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(I8::new(10), I8::new(5), BooleanOperation::LTE).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            I8::boolean_op(I8::new(10), I8::new(5), BooleanOperation::GTE).unwrap(),
            Value::from(true)
        );
        assert_eq!(
            I8::boolean_op(I8::new(10), I8::new(5), BooleanOperation::EQ).unwrap(),
            Value::from(false)
        );
        assert_eq!(
            I8::boolean_op(I8::new(10), I8::new(5), BooleanOperation::NEQ).unwrap(),
            Value::from(true)
        );
        assert_eq!(I8::boolean_not(I8::new(10)).unwrap(), Value::from(false));
    }

    #[test]
    fn test_bitwise() {
        assert_eq!(
            I8::bitwise_op(I8::new(10), I8::new(5), BitwiseOperation::And).unwrap(),
            I8::new(0)
        );
        assert_eq!(
            I8::bitwise_op(I8::new(10), I8::new(5), BitwiseOperation::Or).unwrap(),
            I8::new(15)
        );
        assert_eq!(
            I8::bitwise_op(I8::new(10), I8::new(5), BitwiseOperation::Xor).unwrap(),
            I8::new(15)
        );
        assert_eq!(
            I8::bitwise_op(I8::new(10), I8::new(1), BitwiseOperation::LeftShift).unwrap(),
            I8::new(20)
        );
        assert_eq!(
            I8::bitwise_op(I8::new(10), I8::new(5), BitwiseOperation::RightShift).unwrap(),
            I8::new(0)
        );
        assert_eq!(
            I8::bitwise_op(I8::new(10), I8::new(-5), BitwiseOperation::LeftShift).unwrap(),
            I8::new(0)
        );
        assert_eq!(
            I8::bitwise_op(I8::new(10), I8::new(-1), BitwiseOperation::RightShift).unwrap(),
            I8::new(20)
        );
        assert_eq!(I8::bitwise_not(I8::new(-10)).unwrap(), I8::new(9));
    }

    #[test]
    fn test_arithmetic() {
        assert_eq!(
            I8::arithmetic_op(I8::new(10), I8::new(5), ArithmeticOperation::Add).unwrap(),
            I8::new(15)
        );
        assert_eq!(
            I8::arithmetic_op(I8::new(10), I8::new(5), ArithmeticOperation::Subtract).unwrap(),
            I8::new(5)
        );
        assert_eq!(
            I8::arithmetic_op(I8::new(10), I8::new(5), ArithmeticOperation::Multiply).unwrap(),
            I8::new(50)
        );
        assert_eq!(
            I8::arithmetic_op(I8::new(10), I8::new(5), ArithmeticOperation::Divide).unwrap(),
            I8::new(2)
        );
        assert_eq!(
            I8::arithmetic_op(I8::new(10), I8::new(5), ArithmeticOperation::Modulo).unwrap(),
            I8::new(0)
        );
        I8::arithmetic_op(I8::new(10), I8::new(5), ArithmeticOperation::Exponentiate).unwrap_err();
        I64::arithmetic_op(
            I64::new(10),
            I64::new(i64::MAX),
            ArithmeticOperation::Exponentiate,
        )
        .unwrap_err();

        U8::arithmetic_neg(U8::new(10)).unwrap_err();
        assert_eq!(I8::arithmetic_neg(I8::new(10)).unwrap(), I8::new(-10));
    }

    #[test]
    fn test_from_str() {
        assert_eq!(I8::from_str_radix("0b1010").unwrap(), I8::new(10));
        I8::from_str_radix("0b10000000000000").unwrap_err();
        U8::from_str_radix("0b-1").unwrap_err();
        assert_eq!(I8::from_str_radix("03").unwrap(), I8::new(3));
        U8::from_str_radix("256").unwrap_err();
        assert_eq!(I8::from_str_radix("0b1000_0000").unwrap(), I8::new(-128));

        assert_eq!(I16::from_str_radix("0b1010").unwrap(), I16::new(10));
        I16::from_str_radix("0b10000000000000000").unwrap_err();

        assert_eq!(I32::from_str_radix("0b1010").unwrap(), I32::new(10));
        assert_eq!(I32::from_str_radix("0b1").unwrap(), I32::new(1));

        assert_eq!(I8::from_str_radix("0b1000_0000").unwrap(), I8::new(-128));
        assert_eq!(I8::from_str_radix("0b1000_0001").unwrap(), I8::new(-127));
        assert_eq!(I8::from_str_radix("0b1000_0010").unwrap(), I8::new(-126));

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

        assert_eq!(I8::from_str_radix("0").unwrap(), I8::new(0));
        assert_eq!(I8::from_str_radix("0o").unwrap(), I8::new(0));
        I8::from_str_radix("1x1").unwrap_err();
        I8::from_str_radix("0n1").unwrap_err();
        I8::from_str_radix("0xFFF").unwrap_err();

        let mut u = U64::from_str_radix("0b11111").unwrap();
        *u.inner_mut() = 32;
        assert_eq!(u, U64::new(32));

        assert_eq!(I8::from_str("10").unwrap(), I8::new(10));
        assert_eq!(I16::from_str("10_000").unwrap(), I16::new(10000));
        I8::from_str("10_000").unwrap_err();
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

    #[test]
    #[allow(overflowing_literals)]
    fn test_special_shifting() {
        macro_rules! test_shift {
            (LL: $input:expr, $expected:expr) => {
                assert_eq!(
                    U8::new($input).logical_lshift(1).unwrap(),
                    U8::new($expected),
                    "\n{:0b}u8 << 1: {:0b} != {:0b}",
                    $input,
                    U8::new($input).logical_lshift(1).unwrap().inner(),
                    $expected
                );
                assert_eq!(
                    I8::new($input).logical_lshift(1).unwrap(),
                    I8::new($expected),
                    "\n{:0b}i8 << 1: {:0b} != {:0b}",
                    $input,
                    I8::new($input).logical_lshift(1).unwrap().inner(),
                    $expected
                );
            };
            (LR: $input:expr, $expected:expr) => {
                assert_eq!(
                    U8::new($input).logical_rshift(1).unwrap(),
                    U8::new($expected),
                    "\n{:0b}u8 >> 1: {:0b} != {:0b}",
                    $input,
                    U8::new($input).logical_rshift(1).unwrap().inner(),
                    $expected
                );
                assert_eq!(
                    I8::new($input).logical_rshift(1).unwrap(),
                    I8::new($expected),
                    "\n{:0b}i8 >> 1: {:0b} != {:0b}",
                    $input,
                    I8::new($input).logical_rshift(1).unwrap().inner(),
                    $expected
                );
            };
            (AL: $input:expr, $expected:expr) => {
                assert_eq!(
                    U8::new($input).arithmetic_lshift(1).unwrap(),
                    U8::new($expected),
                    "\n{:0b}u8 <<< 1: {:0b} != {:0b}",
                    $input,
                    U8::new($input).arithmetic_lshift(1).unwrap().inner(),
                    $expected
                );
                assert_eq!(
                    I8::new($input).arithmetic_lshift(1).unwrap(),
                    I8::new($expected),
                    "\n{:0b}i8 <<< 1: {:0b} != {:0b}",
                    $input,
                    I8::new($input).arithmetic_lshift(1).unwrap().inner(),
                    $expected
                );
            };
            (AR: $input:expr, $expected:expr) => {
                assert_eq!(
                    U8::new($input).arithmetic_rshift(1).unwrap(),
                    U8::new($expected),
                    "\n{:0b}u8 >>> 1: {:0b} != {:0b}",
                    $input,
                    U8::new($input).arithmetic_rshift(1).unwrap().inner(),
                    $expected
                );
                assert_eq!(
                    I8::new($input).arithmetic_rshift(1).unwrap(),
                    I8::new($expected),
                    "\n{:0b}i8 >>> 1: {:0b} != {:0b}",
                    $input,
                    I8::new($input).arithmetic_rshift(1).unwrap().inner(),
                    $expected
                );
            };
        }

        test_shift!(AL: 0b1000_0000, 0b1000_0000);
        test_shift!(AL: 0b0100_0000, 0b0000_0000);
        test_shift!(AR: 0b1001_0000, 0b1000_1000);
        test_shift!(LL: 0b0100_0000, 0b1000_0000);
        test_shift!(LR: 0b1000_0000, 0b0100_0000);
    }
}
