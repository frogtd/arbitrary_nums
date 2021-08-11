#![deny(clippy::panic)]
#![allow(non_camel_case_types)]
#![warn(unsafe_op_in_unsafe_fn)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use std::error::Error;

use core::{
    cmp,
    convert::{TryFrom, TryInto},
    fmt::{Binary, Debug, Display, LowerExp, LowerHex, Octal},
    iter::{Product, Sum},
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroU128, NonZeroU16,
        NonZeroU32, NonZeroU64, NonZeroU8,
    },
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
};

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[rustfmt::skip]
#[allow(dead_code)]
enum InnerU1 {
    Hex00, Hex01
}

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct u1(InnerU2);

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[rustfmt::skip]
#[allow(dead_code)]
enum InnerU2 {
    Hex00, Hex01, Hex02, Hex03,
}
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct u2(InnerU2);

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[rustfmt::skip]
#[allow(dead_code)]
enum InnerU3 {
    Hex00, Hex01, Hex02, Hex03, Hex04, Hex05, Hex06, Hex07,
}
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]

pub struct u3(InnerU3);

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[rustfmt::skip]
#[allow(dead_code)]
enum InnerU4 {
    Hex00, Hex01, Hex02, Hex03, Hex04, Hex05, Hex06, Hex07,
    Hex08, Hex09, Hex0A, Hex0B, Hex0C, Hex0D, Hex0E, Hex0F,
}
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]

pub struct u4(InnerU4);

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[rustfmt::skip]
#[allow(dead_code)]
enum InnerU5 {
    Hex00, Hex01, Hex02, Hex03, Hex04, Hex05, Hex06, Hex07,
    Hex08, Hex09, Hex0A, Hex0B, Hex0C, Hex0D, Hex0E, Hex0F,
    Hex10, Hex11, Hex12, Hex13, Hex14, Hex15, Hex16, Hex17,
    Hex18, Hex19, Hex1A, Hex1B, Hex1C, Hex1D, Hex1E, Hex1F,
}
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct u5(InnerU5);
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]

#[rustfmt::skip]
#[allow(dead_code)]
enum InnerU6 {
    Hex00, Hex01, Hex02, Hex03, Hex04, Hex05, Hex06, Hex07,
    Hex08, Hex09, Hex0A, Hex0B, Hex0C, Hex0D, Hex0E, Hex0F,
    Hex10, Hex11, Hex12, Hex13, Hex14, Hex15, Hex16, Hex17,
    Hex18, Hex19, Hex1A, Hex1B, Hex1C, Hex1D, Hex1E, Hex1F,
    Hex20, Hex21, Hex22, Hex23, Hex24, Hex25, Hex26, Hex27,
    Hex28, Hex29, Hex2A, Hex2B, Hex2C, Hex2D, Hex2E, Hex2F,
    Hex30, Hex31, Hex32, Hex33, Hex34, Hex35, Hex36, Hex37,
    Hex38, Hex39, Hex3A, Hex3B, Hex3C, Hex3D, Hex3E, Hex3F,
}
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]

pub struct u6(InnerU6);

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[rustfmt::skip]
#[allow(dead_code)]
enum InnerU7 {
    Hex00, Hex01, Hex02, Hex03, Hex04, Hex05, Hex06, Hex07,
    Hex08, Hex09, Hex0A, Hex0B, Hex0C, Hex0D, Hex0E, Hex0F,
    Hex10, Hex11, Hex12, Hex13, Hex14, Hex15, Hex16, Hex17,
    Hex18, Hex19, Hex1A, Hex1B, Hex1C, Hex1D, Hex1E, Hex1F,
    Hex20, Hex21, Hex22, Hex23, Hex24, Hex25, Hex26, Hex27,
    Hex28, Hex29, Hex2A, Hex2B, Hex2C, Hex2D, Hex2E, Hex2F,
    Hex30, Hex31, Hex32, Hex33, Hex34, Hex35, Hex36, Hex37,
    Hex38, Hex39, Hex3A, Hex3B, Hex3C, Hex3D, Hex3E, Hex3F,
    Hex40, Hex41, Hex42, Hex43, Hex44, Hex45, Hex46, Hex47,
    Hex48, Hex49, Hex4A, Hex4B, Hex4C, Hex4D, Hex4E, Hex4F,
    Hex50, Hex51, Hex52, Hex53, Hex54, Hex55, Hex56, Hex57,
    Hex58, Hex59, Hex5A, Hex5B, Hex5C, Hex5D, Hex5E, Hex5F,
    Hex60, Hex61, Hex62, Hex63, Hex64, Hex65, Hex66, Hex67,
    Hex68, Hex69, Hex6A, Hex6B, Hex6C, Hex6D, Hex6E, Hex6F,
    Hex70, Hex71, Hex72, Hex73, Hex74, Hex75, Hex76, Hex77,
    Hex78, Hex79, Hex7A, Hex7B, Hex7C, Hex7D, Hex7E, Hex7F,
}
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct u7(InnerU7);

#[derive(Debug, PartialEq)]
pub struct IntFromError(());

impl Display for IntFromError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Coming from int Failed")
    }
}
#[cfg(feature = "std")]
impl Error for IntFromError {}

#[derive(Debug, PartialEq)]
pub enum ParseIntError {
    Empty,
    PosOverflow,
    NegOverflow,
    InvalidDigit,
}

impl Display for ParseIntError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self)
    }
}
#[cfg(feature = "std")]
impl Error for ParseIntError {}

macro_rules! new_wrapper {
    ($func_name:ident, $var_name:ident, $type:ty) => {
        pub const fn $func_name(self, $var_name: $type) -> Option<Self> {
            Self::new_option(self.as_byte().$func_name($var_name))
        }
    };
    ($func_name:ident, $var_name:ident, $type:ty, $other_func:ident) => {
        pub const fn $func_name(self, $var_name: $type) -> Option<Self> {
            Self::new_option(self.as_byte().$func_name($var_name.$other_func()))
        }
    };
    ($func_name:ident, $var_name:ident, $type:ty, $other_func:ident, $out:ty) => {
        pub const fn $func_name(self, $var_name: $type) -> $out {
            Self::new_option(self.as_byte().$func_name($var_name.$other_func()))
        }
    };
}
macro_rules! new_wrapper_no_arg {
    ($func_name:ident, $out:ty, $ex:expr) => {
        pub const fn $func_name(self) -> $out {
            self.as_byte().$func_name() - $ex
        }
    };

    ($func_name:ident, $out:ty) => {
        pub const fn $func_name(self) -> $out {
            self.as_byte().$func_name()
        }
    };
}
macro_rules! new_wrapper_overflowing {
    ($func_name:ident) => {
        pub const fn $func_name(self, rhs: Self) -> (Self, bool) {
            let (value, overflowed) = self.as_byte().$func_name(rhs.as_byte());
            (
                Self::new_infallible(value),
                overflowed && Self::overflowed(value),
            )
        }
    };

    ($func_name:ident, :) => {
        pub const fn $func_name(self) -> (Self, bool) {
            let (value, overflowed) = self.as_byte().$func_name();
            (
                Self::new_infallible(value),
                overflowed && Self::overflowed(value),
            )
        }
    };

    ($func_name:ident, $type:ty) => {
        pub const fn $func_name(self, rhs: $type) -> (Self, bool) {
            let (value, overflowed) = self.as_byte().$func_name(rhs);
            (
                Self::new_infallible(value),
                overflowed && Self::overflowed(value),
            )
        }
    };
}

macro_rules! new_wrapper_wrapping {
    ($func_name:ident) => {
        pub const fn $func_name(self, rhs: Self) -> Self {
            Self::new_infallible(self.as_byte().$func_name(rhs.as_byte()))
        }
    };
    ($func_name:ident, :) => {
        pub const fn $func_name(self) -> Self {
            Self::new_infallible(self.as_byte().$func_name())
        }
    };
    ($func_name:ident, $type:ty) => {
        pub const fn $func_name(self, rhs: $type) -> Self {
            Self::new_infallible(self.as_byte().$func_name(rhs))
        }
    };
}
macro_rules! try_from_type {
    ($typefrom:ty, $typeinto:ty) => {
        impl TryFrom<$typefrom> for $typeinto {
            type Error = IntFromError;

            fn try_from(value: $typefrom) -> Result<Self, Self::Error> {
                let value = value.try_into().map_err(|_| IntFromError(()))?;
                Self::new(value).ok_or(IntFromError(()))
            }
        }
    };

    ($typefrom:ty, $typeinto:ty, :) => {
        impl TryFrom<$typefrom> for $typeinto {
            type Error = IntFromError;

            fn try_from(value: $typefrom) -> Result<Self, Self::Error> {
                let value = value.get().try_into().map_err(|_| IntFromError(()))?;
                Self::new(value).ok_or(IntFromError(()))
            }
        }
    };
}

macro_rules! type_from {
    ($typefrom:ty, $typeinto:ty) => {
        impl From<$typefrom> for $typeinto {
            fn from(n: $typefrom) -> Self {
                n.0 as $typeinto
            }
        }
    };
}
macro_rules! op_impl {
    ($type:ty, $trait:ident, $method:ident) => {
        impl $trait for $type {
            type Output = $type;

            fn $method(self, rhs: Self) -> Self::Output {
                Self::new_debug_assertion(u8::$method(self.as_byte(), rhs.as_byte()))
            }
        }
        impl $trait<&'_ $type> for &'_ $type {
            type Output = $type;

            fn $method(self, rhs: &'_ $type) -> Self::Output {
                $trait::$method(*self, *rhs)
            }
        }

        impl $trait<&'_ $type> for $type {
            type Output = $type;

            fn $method(self, rhs: &'_ $type) -> Self::Output {
                $trait::$method(self, *rhs)
            }
        }
        impl $trait<$type> for &'_ $type {
            type Output = $type;

            fn $method(self, rhs: $type) -> Self::Output {
                $trait::$method(*self, rhs)
            }
        }
    };
    ($type:ty, $other_type:ty, $trait:ident, $method:ident) => {
        impl $trait<$other_type> for $type {
            type Output = $type;

            fn $method(self, rhs: $other_type) -> Self::Output {
                Self::new_debug_assertion(u8::$method(self.as_byte(), rhs))
            }
        }
        op_impl! {$type, $other_type, $trait, $method, :}
    };
    ($type:ty, $other_type:ty, $trait:ident, $method:ident, :) => {
        impl $trait<&'_ $other_type> for &'_ $type {
            type Output = $type;

            fn $method(self, rhs: &'_ $other_type) -> Self::Output {
                $trait::$method(*self, *rhs)
            }
        }

        impl $trait<&'_ $other_type> for $type {
            type Output = $type;

            fn $method(self, rhs: &'_ $other_type) -> Self::Output {
                $trait::$method(self, *rhs)
            }
        }
        impl $trait<$other_type> for &'_ $type {
            type Output = $type;

            fn $method(self, rhs: $other_type) -> Self::Output {
                $trait::$method(*self, rhs)
            }
        }
    };
    ($type:ty, $other_type:ty, $trait:ident, $method:ident, #) => {
        impl $trait<$other_type> for $type {
            type Output = $type;

            fn $method(self, rhs: $other_type) -> Self::Output {
                Self::new_debug_assertion(u8::$method(self.as_byte(), rhs.as_byte()))
            }
        }
        op_impl! {$type, $other_type, $trait, $method, :}
    };
}
macro_rules! fmt_wrap {
    ($trait:ident, $type:ty) => {
        impl $trait for $type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                $trait::fmt(&self.as_byte(), f)
            }
        }
    };
}

macro_rules! assign_impl {
    ($type:ty, $trait:ident, $trait_method:ident, $other_trait_method:ident) => {
        assign_impl! { $type, Self, $trait, $trait_method, $other_trait_method }
    };

    ($type:ty, $other_type:ty, $trait:ident, $trait_method:ident, $other_trait_method:ident) => {
        impl $trait<$other_type> for $type {
            fn $trait_method(&mut self, rhs: $other_type) {
                *self = Self::$other_trait_method(*self, rhs)
            }
        }
        impl $trait<&'_ $other_type> for $type {
            fn $trait_method(&mut self, rhs: &'_ $other_type) {
                *self = Self::$other_trait_method(*self, *rhs)
            }
        }
    };
}

macro_rules! impl_functions {
    ($type:ty, $min:expr, $max:expr) => {
        impl $type {
            /// The smallest value that can be represented by this integer type.
            pub const MIN: Self = unsafe { Self::new_unchecked($min) };
            pub const MAX: Self = unsafe { Self::new_unchecked($max) };
            pub const BITS: u32 = 4;
            /// # Safety
            /// `n` must be between
            #[doc = concat!("`", $min, "` and `", $max, "`.")]
            pub const unsafe fn new_unchecked(n: u8) -> Self {
                unsafe { core::mem::transmute(n) }
            }
            pub const fn new(n: u8) -> Option<Self> {
                if n > 0xF {
                    None
                } else {
                    Some(unsafe { Self::new_unchecked(n) })
                }
            }
            pub const fn new_infallible(n: u8) -> Self {
                unsafe { Self::new_unchecked(n & Self::MAX.as_byte()) }
            }

            pub const fn checked_add(self, rhs: Self) -> Option<Self> {
                Self::new(rhs.as_byte().wrapping_add(self.as_byte()))
            }
            new_wrapper! {checked_div, exp, Self, as_byte}
            new_wrapper! {checked_div_euclid, exp, Self, as_byte}
            new_wrapper! {checked_mul, exp, Self, as_byte}

            pub const fn checked_neg(self) -> Option<Self> {
                if self.as_byte() == 0x0 {
                    Some(Self::MIN)
                } else {
                    None
                }
            }

            pub const fn checked_next_power_of_two(self) -> Option<Self> {
                Self::new(self.as_byte().next_power_of_two())
            }

            new_wrapper! { checked_pow, exp, u32}
            new_wrapper! { checked_rem, exp, u8}
            new_wrapper! { checked_rem_euclid, exp, u8}
            new_wrapper! { checked_shl, exp, u32}
            new_wrapper! { checked_shr, exp, u32}
            new_wrapper! { checked_sub, exp, Self, as_byte}
            new_wrapper_no_arg! { count_ones, u32}
            new_wrapper_no_arg! { count_zeros, u32, (u8::BITS - Self::BITS)}
            pub const fn div_euclid(self, rhs: Self) -> Self {
                unsafe { Self::new_unchecked(self.as_byte() / rhs.as_byte()) }
            }
            pub const fn from_be(x: Self) -> Self {
                x
            }

            pub const fn from_be_bytes(bytes: [u8; 1]) -> Self {
                Self::from_le_bytes(bytes)
            }

            pub const fn from_le(x: Self) -> Self {
                x
            }

            pub const fn from_le_bytes(bytes: [u8; 1]) -> Self {
                unsafe { Self::new_unchecked(bytes[0] & Self::MAX.as_byte()) }
            }

            pub const fn from_ne_bytes(bytes: [u8; 1]) -> Self {
                Self::from_le_bytes(bytes)
            }

            pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
                assert!(
                    ($min..cmp::max(36, $max)).contains(&radix),
                    "radix not in correct range"
                );
                let src = src.as_bytes();
                if src.is_empty() {
                    return Err(ParseIntError::Empty);
                }
                let digits = match src[0] {
                    b'+' => &src[1..],
                    b'-' => {
                        for x in &src[1..] {
                            if *x != b'0' {
                                if (*x as char).is_digit(radix) {
                                    return Err(ParseIntError::NegOverflow);
                                }
                                return Err(ParseIntError::InvalidDigit);
                            }
                        }
                        return Ok(Self::MIN);
                    }
                    _ => src,
                };

                let mut result = Self::MIN;
                for &c in digits {
                    let x = match (c as char).to_digit(radix) {
                        Some(x) => x,
                        None => return Err(ParseIntError::InvalidDigit),
                    };
                    result = match result.checked_mul(radix.try_into().unwrap()) {
                        Some(result) => result,
                        None => return Err(ParseIntError::PosOverflow),
                    };
                    result = match result.checked_add(x.try_into().unwrap()) {
                        Some(result) => result,
                        None => return Err(ParseIntError::PosOverflow),
                    };
                }
                Ok(result)
            }
            new_wrapper_no_arg! {is_power_of_two, bool}
            pub const fn leading_ones(self) -> u32 {
                (self.as_byte() << (u8::BITS - Self::BITS)).leading_ones()
            }

            new_wrapper_no_arg! {leading_zeros, u32, (u8::BITS - Self::BITS)}

            pub const fn next_power_of_two(self) -> Self {
                let number_of_bits_to_end = Self::BITS - self.leading_zeros();
                if cfg!(debug_assertions) {
                    let _ = Self::BITS - number_of_bits_to_end - 1;
                }
                Self::new_infallible(1_u8 << number_of_bits_to_end)
            }
            pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
                let a = self.as_byte().wrapping_add(rhs.as_byte());
                (Self::new_infallible(a), Self::overflowed(a))
            }

            new_wrapper_overflowing! { overflowing_div }
            new_wrapper_overflowing! { overflowing_div_euclid }
            new_wrapper_overflowing! { overflowing_mul }
            new_wrapper_overflowing! { overflowing_neg, : }
            new_wrapper_overflowing! { overflowing_pow, u32 }
            new_wrapper_overflowing! { overflowing_rem }
            new_wrapper_overflowing! { overflowing_rem_euclid }
            new_wrapper_overflowing! { overflowing_shl, u32 }
            new_wrapper_overflowing! { overflowing_shr, u32 }
            new_wrapper_overflowing! { overflowing_sub }

            pub const fn pow(self, exp: u32) -> Self {
                Self::new_debug_assertion(self.as_byte().pow(exp))
            }

            pub const fn rem_euclid(self, rhs: Self) -> Self {
                unsafe { Self::new_unchecked(self.as_byte() % rhs.as_byte()) }
            }
            pub const fn reverse_bits(self) -> Self {
                let a = self.as_byte().reverse_bits();
                unsafe { Self::new_unchecked(a.wrapping_shr(u8::BITS - Self::BITS)) }
            }
            pub const fn rotate_left(self, n: u32) -> Self {
                let a = self.as_byte().wrapping_shl(n % Self::BITS);
                let b = self.as_byte().wrapping_shr(Self::BITS - (n % Self::BITS));
                Self::new_infallible(a | b)
            }
            pub const fn rotate_right(self, n: u32) -> Self {
                let a = self.as_byte().wrapping_shr(n % Self::BITS);
                let b = self.as_byte().wrapping_shl(Self::BITS - (n % Self::BITS));
                Self::new_infallible(a | b)
            }
            pub const fn saturating_add(self, rhs: Self) -> Self {
                let (value, overflowed) = Self::overflowing_add(self, rhs);
                if overflowed {
                    Self::MAX
                } else {
                    value
                }
            }
            pub const fn saturating_mul(self, rhs: Self) -> Self {
                let (value, overflowed) = Self::overflowing_mul(self, rhs);
                if overflowed {
                    Self::MAX
                } else {
                    value
                }
            }
            pub const fn saturating_pow(self, rhs: u32) -> Self {
                let (value, overflowed) = Self::overflowing_pow(self, rhs);
                if overflowed {
                    Self::MAX
                } else {
                    value
                }
            }

            pub const fn saturating_sub(self, rhs: Self) -> Self {
                let (value, overflowed) = Self::overflowing_sub(self, rhs);
                if overflowed {
                    Self::MIN
                } else {
                    value
                }
            }
            pub const fn swap_bytes(self) -> Self {
                self
            }

            pub const fn to_be(x: Self) -> Self {
                x
            }
            pub const fn to_be_bytes(self) -> [u8; 1] {
                [self.0 as u8]
            }
            pub const fn to_le(x: Self) -> Self {
                x
            }
            pub const fn to_le_bytes(self) -> [u8; 1] {
                [self.0 as u8]
            }
            pub const fn to_ne_bytes(self) -> [u8; 1] {
                [self.0 as u8]
            }

            new_wrapper_no_arg! {trailing_ones, u32}

            pub const fn trailing_zeros(self) -> u32 {
                let mut a = self.as_byte();
                a |= !Self::MAX.as_byte();
                a.trailing_zeros()
            }

            new_wrapper_wrapping! { wrapping_add }
            new_wrapper_wrapping! { wrapping_div }
            new_wrapper_wrapping! { wrapping_div_euclid }
            new_wrapper_wrapping! { wrapping_mul }
            new_wrapper_wrapping! { wrapping_neg, : }
            new_wrapper_wrapping! { wrapping_pow, u32 }
            new_wrapper_wrapping! { wrapping_rem }
            new_wrapper_wrapping! { wrapping_rem_euclid }
            new_wrapper_wrapping! { wrapping_shl, u32 }
            new_wrapper_wrapping! { wrapping_shr, u32 }
            new_wrapper_wrapping! { wrapping_sub }
            pub const fn as_byte(self) -> u8 {
                self.0 as u8
            }

            const fn new_option(n: Option<u8>) -> Option<Self> {
                match n {
                    Some(x) => Self::new(x),
                    None => None,
                }
            }
            const fn overflowed(a: u8) -> bool {
                a & !Self::MAX.as_byte() != 0
            }
            const fn new_debug_assertion(n: u8) -> Self {
                if cfg!(debug_assertions) {
                    let result = Self::new(n);
                    #[allow(clippy::unnecessary_operation)]
                    {
                        [()][result.is_none() as usize];
                    }
                    unsafe { Self::new_unchecked(n) }
                } else {
                    Self::new_infallible(n)
                }
            }
        }
        impl TryFrom<u8> for $type {
            type Error = IntFromError;

            fn try_from(value: u8) -> Result<Self, Self::Error> {
                Self::new(value).ok_or(IntFromError(()))
            }
        }
        impl Default for $type {
            fn default() -> Self {
                Self::MIN
            }
        }
        impl Not for $type {
            type Output = $type;

            fn not(self) -> Self::Output {
                Self::new_infallible(!self.as_byte())
            }
        }
        fmt_wrap! { Display, $type }
        fmt_wrap! { Debug, $type }
        fmt_wrap! { Binary, $type }
        fmt_wrap! { Octal, $type }
        fmt_wrap! { LowerExp, $type }
        fmt_wrap! { LowerHex, $type }
        try_from_type! { NonZeroU8, $type, : }
        try_from_type! { NonZeroU16, $type, : }
        try_from_type! { NonZeroU32, $type, : }
        try_from_type! { NonZeroU64, $type, : }
        try_from_type! { NonZeroU128, $type, : }
        try_from_type! { NonZeroI8, $type, : }
        try_from_type! { NonZeroI16, $type, : }
        try_from_type! { NonZeroI32, $type, : }
        try_from_type! { NonZeroI64, $type, : }
        try_from_type! { NonZeroI128, $type, : }
        try_from_type! { u16, $type }
        try_from_type! { u32, $type }
        try_from_type! { u64, $type }
        try_from_type! { u128, $type }
        try_from_type! { i8, $type }
        try_from_type! { i16, $type }
        try_from_type! { i32, $type }
        try_from_type! { i64, $type }
        try_from_type! { i128, $type }
        impl From<bool> for $type {
            fn from(n: bool) -> Self {
                unsafe { Self::new_unchecked(n as u8) }
            }
        }

        type_from! { $type, u16 }
        type_from! { $type, u32 }
        type_from! { $type, u64 }
        type_from! { $type, u128 }
        type_from! { $type, i8 }
        type_from! { $type, i16 }
        type_from! { $type, i32 }
        type_from! { $type, i64 }
        type_from! { $type, i128 }
        op_impl! { $type, Add, add }
        op_impl! { $type, Mul, mul }
        op_impl! { $type, BitAnd, bitand }
        op_impl! { $type, BitOr, bitor }
        op_impl! { $type, BitXor, bitxor }
        op_impl! { $type, Sub, sub }
        op_impl! { $type, Rem, rem }
        op_impl! { $type, Div, div }
        impl Product for $type {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::new(0).unwrap(), |a, b| a * b)
            }
        }

        impl Sum for $type {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::new(0).unwrap(), |a, b| a + b)
            }
        }
        op_impl! { $type, u16, Shl, shl }
        op_impl! { $type, u32, Shl, shl }
        op_impl! { $type, u64, Shl, shl }
        op_impl! { $type, u128, Shl, shl }
        op_impl! { $type, i8, Shl, shl }
        op_impl! { $type, i16, Shl, shl }
        op_impl! { $type, i32, Shl, shl }
        op_impl! { $type, i64, Shl, shl }
        op_impl! { $type, i128, Shl, shl }
        op_impl! { $type, u1, Shl, shl, # }
        op_impl! { $type, u2, Shl, shl, # }
        op_impl! { $type, u3, Shl, shl, # }
        op_impl! { $type, u4, Shl, shl, # }
        op_impl! { $type, u5, Shl, shl, # }
        op_impl! { $type, u6, Shl, shl, # }
        op_impl! { $type, u7, Shl, shl, # }
        op_impl! { $type, u16, Shr, shr }
        op_impl! { $type, u32, Shr, shr }
        op_impl! { $type, u64, Shr, shr }
        op_impl! { $type, u128, Shr, shr }
        op_impl! { $type, i8, Shr, shr }
        op_impl! { $type, i16, Shr, shr }
        op_impl! { $type, i32, Shr, shr }
        op_impl! { $type, i64, Shr, shr }
        op_impl! { $type, i128, Shr, shr }
        op_impl! { $type, u1, Shr, shr, # }
        op_impl! { $type, u2, Shr, shr, # }
        op_impl! { $type, u3, Shr, shr, # }
        op_impl! { $type, u4, Shr, shr, # }
        op_impl! { $type, u5, Shr, shr, # }
        op_impl! { $type, u6, Shr, shr, # }
        op_impl! { $type, u7, Shr, shr, # }

        assign_impl! { $type, AddAssign, add_assign, add }
        assign_impl! { $type, BitAndAssign, bitand_assign, bitand }
        assign_impl! { $type, BitOrAssign, bitor_assign, bitor }
        assign_impl! { $type, BitXorAssign, bitxor_assign, bitxor }
        assign_impl! { $type, DivAssign, div_assign, div }
        assign_impl! { $type, MulAssign, mul_assign, mul }
        assign_impl! { $type, RemAssign, rem_assign, rem }
        assign_impl! { $type, SubAssign, sub_assign, sub }
        assign_impl! { $type, u16, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u32, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u64, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u128, ShlAssign, shl_assign, shl }
        assign_impl! { $type, i8, ShlAssign, shl_assign, shl }
        assign_impl! { $type, i16, ShlAssign, shl_assign, shl }
        assign_impl! { $type, i32, ShlAssign, shl_assign, shl }
        assign_impl! { $type, i64, ShlAssign, shl_assign, shl }
        assign_impl! { $type, i128, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u1, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u2, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u3, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u4, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u5, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u6, ShlAssign, shl_assign, shl }
        assign_impl! { $type, u7, ShlAssign, shl_assign, shl }

        assign_impl! { $type, u16, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u32, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u64, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u128, ShrAssign, shr_assign, shr }
        assign_impl! { $type, i8, ShrAssign, shr_assign, shr }
        assign_impl! { $type, i16, ShrAssign, shr_assign, shr }
        assign_impl! { $type, i32, ShrAssign, shr_assign, shr }
        assign_impl! { $type, i64, ShrAssign, shr_assign, shr }
        assign_impl! { $type, i128, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u1, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u2, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u3, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u4, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u5, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u6, ShrAssign, shr_assign, shr }
        assign_impl! { $type, u7, ShrAssign, shr_assign, shr }
    };
}
impl_functions! { u1, 0x0, 0x1 }
impl_functions! { u2, 0x0, 0x3 }
impl_functions! { u3, 0x0, 0x7 }
impl_functions! { u4, 0x0, 0xF }
impl_functions! { u5, 0x0, 0x1F }
impl_functions! { u6, 0x0, 0x3F }
impl_functions! { u7, 0x0, 0x7F }
