/// A macro that generates birectional converters between a type and Value
/// It will be a `TryFrom<Value> for Source` and `Into<Value> for Source` implementation
/// and take in 3 parameters:
/// - `source`: The type to convert from/to
/// - `into`: A closure that takes in a `Source` and returns a `Value`
/// - `from`: A closure that takes in a `Value` and returns a `Result<Source, Error>`
macro_rules! map_value {
    (from = $target:ty, handle_into = ($ival:ident) $into:block, handle_from = ($fval:ident) $from:block) => {
        impl TryFrom<$crate::Value> for $target {
            type Error = crate::Error;

            fn try_from($fval: $crate::Value) -> Result<Self, Self::Error> $from
        }

        impl From<$target> for $crate::Value {
            fn from($ival: $target) -> Self $into
        }
    };
}

///
/// A macro that generates a subtype converter for a given type.
/// It will be a `TryFrom<Target> for Source`` implementation
/// and take in 4 parameters:
/// - `target`: The type to convert to
/// - `source`: The type to convert from
/// - `handler`: A closure that takes in a `Source` and returns a `Result<Target, Error>`
macro_rules! map_type {
    (Int, $source:ty) => {
        map_type!(U8, $source);
        map_type!(U16, $source);
        map_type!(U32, $source);
        map_type!(U64, $source);

        map_type!(I8, $source);
        map_type!(I16, $source);
        map_type!(I32, $source);
        map_type!(I64, $source);
    };

    ($target:ty, $source:ty) => {
        impl TryFrom<$target> for $source {
            type Error = crate::Error;
            fn try_from(value: $target) -> Result<Self, Self::Error> {
                Ok(Self::try_from(Value::from(value))?)
            }
        }
    };
}

///
/// A macro that generates a primitive converter for a given type.
/// It will be a `From<Primitive>/Into<Primitive> for Source` implementation
/// and take in 4 parameters:
/// - `primitive`: The primitive type to convert to/from
/// - `source`: The type to convert from/to
/// - `into`: A closure that takes in a `Source` and returns a `Primitive`
/// - `from`: A closure that takes in a `Primitive` and returns a `Source`
macro_rules! map_primitive {
    (from = $source:ty, primitive = $primitive:ty) => {
        #[allow(clippy::from_over_into)]
        impl Into<$primitive> for $source {
            fn into(self) -> $primitive {
                self.0
            }
        }

        impl From<$primitive> for $source {
            fn from(value: $primitive) -> Self {
                <$source>::new(value)
            }
        }

        impl From<$primitive> for $crate::Value {
            fn from(value: $primitive) -> Self {
                <$source>::new(value).into()
            }
        }

        #[allow(clippy::from_over_into)]
        impl TryInto<$primitive> for $crate::Value {
            type Error = crate::Error;
            fn try_into(self) -> Result<$primitive, Self::Error> {
                let value: $source = self.try_into()?;
                Ok(value.into())
            }
        }
    };
}

/// A macro that generates an implementation of ValueTrait for a given type.
/// Will also generate a Display and Debug implementation for the type.
/// Those implementations will use the `TryInto<Str>` implementation.
macro_rules! impl_value {
    ($own_type:ty, $inner_type:ty, $to_string:expr, $debug:expr) => {
        impl $crate::ValueTrait for $own_type {
            type Inner = $inner_type;

            fn new(inner: $inner_type) -> Self {
                Self(inner)
            }

            fn inner(&self) -> &$inner_type {
                &self.0
            }

            fn inner_mut(&mut self) -> &mut $inner_type {
                &mut self.0
            }

            fn into_inner(self) -> $inner_type {
                self.0
            }
        }

        map_primitive!(from = $own_type, primitive = $inner_type);

        impl std::fmt::Display for $own_type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", $to_string(self))
            }
        }

        impl std::fmt::Debug for $own_type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                $debug(self, f)
            }
        }
    };
    ($own_type:ty, $inner_type:ty, $to_string:expr) => {
        impl_value!(
            $own_type,
            $inner_type,
            $to_string,
            |this: &Self, f: &mut std::fmt::Formatter<'_>| { write!(f, "{}", $to_string(this)) }
        );
    };
}

macro_rules! overload_operator {
    ($type:ident, arithmetic) => {
        overload_operator!($type, add);
        overload_operator!($type, sub);
        overload_operator!($type, mul);
        overload_operator!($type, div);
        overload_operator!($type, rem);
        overload_operator!($type, neg);
    };

    ($type:ident, add) => {
        impl std::ops::Add for $type {
            type Output = Result<Self, crate::Error>;
            fn add(self, rhs: Self) -> Self::Output {
                Self::arithmetic_op(self, rhs, ArithmeticOperation::Add)
            }
        }
    };

    ($type:ident, sub) => {
        impl std::ops::Sub for $type {
            type Output = Result<Self, crate::Error>;
            fn sub(self, rhs: Self) -> Self::Output {
                Self::arithmetic_op(self, rhs, ArithmeticOperation::Subtract)
            }
        }
    };

    ($type:ident, mul) => {
        impl std::ops::Mul for $type {
            type Output = Result<Self, crate::Error>;
            fn mul(self, rhs: Self) -> Self::Output {
                Self::arithmetic_op(self, rhs, ArithmeticOperation::Multiply)
            }
        }
    };

    ($type:ident, div) => {
        impl std::ops::Div for $type {
            type Output = Result<Self, crate::Error>;
            fn div(self, rhs: Self) -> Self::Output {
                Self::arithmetic_op(self, rhs, ArithmeticOperation::Divide)
            }
        }
    };

    ($type:ident, rem) => {
        impl std::ops::Rem for $type {
            type Output = Result<Self, crate::Error>;
            fn rem(self, rhs: Self) -> Self::Output {
                Self::arithmetic_op(self, rhs, ArithmeticOperation::Modulo)
            }
        }
    };

    ($type:ident, neg) => {
        impl std::ops::Neg for $type {
            type Output = Result<Self, crate::Error>;
            fn neg(self) -> Self::Output {
                Self::arithmetic_neg(self)
            }
        }
    };

    // //////////////////////////////////////////////////////////////////////////////////
    ($type:ident, bitwise) => {
        overload_operator!($type, bitand);
        overload_operator!($type, bitor);
        overload_operator!($type, bitxor);
        overload_operator!($type, shl);
        overload_operator!($type, shr);
    };

    ($type:ident, bitand) => {
        impl std::ops::BitAnd for $type {
            type Output = Result<Self, crate::Error>;
            fn bitand(self, rhs: Self) -> Self::Output {
                Self::bitwise_op(self, rhs, BitwiseOperation::And)
            }
        }
    };

    ($type:ident, bitor) => {
        impl std::ops::BitOr for $type {
            type Output = Result<Self, crate::Error>;
            fn bitor(self, rhs: Self) -> Self::Output {
                Self::bitwise_op(self, rhs, BitwiseOperation::Or)
            }
        }
    };

    ($type:ident, bitxor) => {
        impl std::ops::BitXor for $type {
            type Output = Result<Self, crate::Error>;
            fn bitxor(self, rhs: Self) -> Self::Output {
                Self::bitwise_op(self, rhs, BitwiseOperation::Xor)
            }
        }
    };

    ($type:ident, shl) => {
        impl std::ops::Shl for $type {
            type Output = Result<Self, crate::Error>;
            fn shl(self, rhs: Self) -> Self::Output {
                Self::bitwise_op(self, rhs, BitwiseOperation::LeftShift)
            }
        }
    };

    ($type:ident, shr) => {
        impl std::ops::Shr for $type {
            type Output = Result<Self, crate::Error>;
            fn shr(self, rhs: Self) -> Self::Output {
                Self::bitwise_op(self, rhs, BitwiseOperation::RightShift)
            }
        }
    };

    // ///////////////////////////////////////////////////////////////////////////
    ($type:ident, bool_not) => {
        impl std::ops::Not for $type {
            type Output = Result<Value, crate::Error>;
            fn not(self) -> Self::Output {
                Self::boolean_not(self)
            }
        }
    };

    // ///////////////////////////////////////////////////////////////////////////
    ($type:ident, deref) => {
        impl std::ops::Deref for $type {
            type Target = <$type as ValueTrait>::Inner;
            fn deref(&self) -> &Self::Target {
                self.inner()
            }
        }

        impl std::ops::DerefMut for $type {
            fn deref_mut(&mut self) -> &mut Self::Target {
                self.inner_mut()
            }
        }
    };
}
