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
        ($name:ident, $subtype:ident) => {
            #[derive(
                PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Serialize, Deserialize, Default, Debug,
            )]
            /// A subtype of `Value` that represents a specific integer variant
            pub struct $name($subtype);

            impl crate::ValueTrait<$subtype> for $name {
                fn new(inner: $subtype) -> Self {
                    Self(inner)
                }

                fn inner(&self) -> &$subtype {
                    &self.0
                }

                fn inner_mut(&mut self) -> &mut $subtype {
                    &mut self.0
                }
            }

            impl std::fmt::Display for $name {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    write!(f, "{}", self.inner().to_string())
                }
            }

            impl $name {
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

                    let value = IntInner::from_str_radix(&s, radix).map_err(|_| {
                        Error::ValueConversion {
                            src_type: ValueType::String,
                            dst_type: ValueType::Int,
                        }
                    })?;

                    if value > <$subtype>::MAX as IntInner || value < <$subtype>::MIN as IntInner {
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
                        if v > <$subtype>::MAX as u8 || v < <$subtype>::MIN as u8 {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(v as $subtype))
                        }
                    }

                    Value::U16(v) => {
                        let v = *v.inner() as u16;
                        if v > <$subtype>::MAX as u16 || v < <$subtype>::MIN as u16 {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(v as $subtype))
                        }
                    }

                    Value::U32(v) => {
                        let v = *v.inner() as u32;
                        if v > <$subtype>::MAX as u32 || v < <$subtype>::MIN as u32 {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(v as $subtype))
                        }
                    }

                    Value::U64(v) => {
                        let v = *v.inner() as u64;
                        if v > <$subtype>::MAX as u64 || v < <$subtype>::MIN as u64 {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(v as $subtype))
                        }
                    }

                    Value::I8(v) => {
                        let v = *v.inner() as i8;
                        if v > <$subtype>::MAX as i8 || v < <$subtype>::MIN as i8 {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(v as $subtype))
                        }
                    }

                    Value::I16(v) => {
                        let v = *v.inner() as i16;
                        if v > <$subtype>::MAX as i16 || v < <$subtype>::MIN as i16 {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(v as $subtype))
                        }
                    }

                    Value::I32(v) => {
                        let v = *v.inner() as i32;
                        if v > <$subtype>::MAX as i32 || v < <$subtype>::MIN as i32 {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(v as $subtype))
                        }
                    }

                    Value::I64(v) => {
                        let v = *v.inner() as IntInner;
                        if v > <$subtype>::MAX as IntInner || v < <$subtype>::MIN as IntInner {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(v as $subtype))
                        }
                    }

                    Value::Int(v) => {
                        let v = *v.inner();
                        if v > <$subtype>::MAX as IntInner || v < <$subtype>::MIN as IntInner {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(v as $subtype))
                        }
                    }
                    Value::Fixed(v) => {
                        let p = *v.inner();
                        let p: IntInner = p.trunc().coefficient() as IntInner;
                        if p > <$subtype>::MAX as IntInner || p < <$subtype>::MIN as IntInner {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(p as $subtype))
                        }
                    }
                    Value::Float(v) => {
                        let p = *v.inner();
                        let p = p as i64;
                        if p > <$subtype>::MAX as IntInner || p < <$subtype>::MIN as IntInner {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(p as $subtype))
                        }
                    }
                    Value::Currency(v) => {
                        let p = *v.inner().value().inner();
                        let p: IntInner = p.trunc().coefficient() as IntInner;
                        if p > <$subtype>::MAX as IntInner || p < <$subtype>::MIN as IntInner {
                            Err(Error::Overflow)
                        } else {
                            Ok($name::new(p as $subtype))
                        }
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
                        #[allow(unused_comparisons)]
                        ArithmeticOperation::Negate => {
                            if $subtype::MIN < 0 {
                                Some(-(left as i64) as $subtype)
                            } else {
                                return Err(Error::UnsupportedOperation {
                                    operation,
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
        };
    }
}

sized_int_type!(I8, i8);
sized_int_type!(I16, i16);
sized_int_type!(I32, i32);
sized_int_type!(I64, i64);
sized_int_type!(U8, u8);
sized_int_type!(U16, u16);
sized_int_type!(U32, u32);
sized_int_type!(U64, u64);

map_primitive!(from = I8, primitive = i8);
map_primitive!(from = I16, primitive = i16);

map_primitive!(from = U8, primitive = u8);
map_primitive!(from = U16, primitive = u16);
map_primitive!(from = U32, primitive = u32);
map_primitive!(from = U64, primitive = u64);
