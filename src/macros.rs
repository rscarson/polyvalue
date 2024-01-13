/// A macro that generates birectional converters between a type and Value
/// It will be a `TryFrom<Value> for Source` and `Into<Value> for Source` implementation
/// and take in 3 parameters:
/// - `source`: The type to convert from/to
/// - `into`: A closure that takes in a `Source` and returns a `Value`
/// - `from`: A closure that takes in a `Value` and returns a `Result<Source, Error>`
macro_rules! map_value {
    (from = $target:ty, handle_into = $into:expr, handle_from = $from:expr) => {
        impl TryFrom<$crate::Value> for $target {
            type Error = crate::Error;
            #[allow(clippy::redundant_closure_call)]
            fn try_from(value: $crate::Value) -> Result<Self, Self::Error> {
                $from(value)
            }
        }

        impl TryFrom<&$crate::Value> for $target {
            type Error = crate::Error;
            #[allow(clippy::redundant_closure_call)]
            fn try_from(value: &$crate::Value) -> Result<Self, Self::Error> {
                $from(value.clone())
            }
        }

        impl From<$target> for $crate::Value {
            #[allow(clippy::redundant_closure_call)]
            fn from(value: $target) -> Self {
                $into(value)
            }
        }

        impl From<&$target> for $crate::Value {
            #[allow(clippy::redundant_closure_call)]
            fn from(value: &$target) -> Self {
                $into(value.clone())
            }
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
    ($target:ty, $source:ty) => {
        impl TryFrom<$target> for $source {
            type Error = crate::Error;
            fn try_from(value: $target) -> Result<Self, Self::Error> {
                Self::try_from(Value::from(value))
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
                self.inner().clone()
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
    ($own_type:ty, $inner_type:ty, $to_string:expr) => {
        impl $crate::ValueTrait<$inner_type> for $own_type {
            fn new(inner: $inner_type) -> Self {
                Self(inner)
            }

            fn inner(&self) -> &$inner_type {
                &self.0
            }

            fn inner_mut(&mut self) -> &mut $inner_type {
                &mut self.0
            }
        }

        map_primitive!(from = $own_type, primitive = $inner_type);

        impl std::fmt::Display for $own_type {
            #[allow(clippy::redundant_closure_call)]
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", $to_string(self))
            }
        }
    };
}
