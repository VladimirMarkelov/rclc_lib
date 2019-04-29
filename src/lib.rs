//! # Expression calculator
//!
//! Calculator transparently supports operations with different type of numbers,
//! converting to appropriate type when it is needed. For instance,
//! `sqrt(-2)` is automatically converted from integer number `-2` to complex
//! one `-2+0i` and is evaluated to `0+1.4142135623730951i`
//!
//! Extra feature: trigonometric functions support both radians and degrees:
//! * Radians are just float numbers: `sin(pi/2)` returns `1`
//! * Degrees can be written in one of the following forms: `12°30'45"` or `12d30m45s` or `12.5125d`
//!
//! Internally degrees are stored and act as float numbers. They only support
//! their own input format. Output format is always a float number.
//!
//! If two numbers have different types, they are converted to highest type and
//! then the result is calculated. The list of number types starting from highest:
//! * Complex numbers. Two input formats supported: `1+2i` and `1+i2`. `i` can be capital. `j` can
//! be used instead of `i`
//! * Float numbers (degrees are float numbers, too)
//! * Rational numbers
//! * Big integer numbers
//!
//! Note: sometimes higher types are converted to lower ones. It may happen
//! after multiplication, division, and squaring a number. Examples:
//! * `sqr(0+2i)` -> `-4` - automatically complex is converted to float number
//! * `1.5 / 0.5` -> `3` - float to big integer
//! * `1\2 + 1\2` -> `1` - half and half is an integer one
//!
//! The list of supported functions:
//! * trigonometric functions (including inverted ones): sin, cos, tan, asin, acos, atan
//! * hyperbolic functions (including inverted ones): sinh, cosh, tanh, asinh, acosh, atanh
//! * square and square root: sqr and sqrt
//! * exponent, logarithm: exp, ln
//! * complex functions: norm, re, im, conjugate
//! * rounding: ceil, floor, trunc, round
//! * float to rational: ratio
//! * absolute value and sign: abs, signum
//! * fractional part of a float number: fract
//!
//! Operators (starting from highest priority):
//! * `!` - factorial (when used after a number or closing bracket)
//! * `-` - unary minus
//! * `**` - power
//! * `*`, `/`, `//` - multiplication, division, integer division
//! * `+`, `-` - addition, subtraction
//! * `&`, `^` - bitwise AND and XOR
//! * `|`, `<<`, `>>` - bitwise OR, SHL, and SHR
//! * `==`, `!=`, `>`, `<`, `>=`, and `<=` - comparison operators
//!
//! Predefined constants:
//! * `PI` - 3.14159...
//! * `E` - 2.71828...
//! * `PHI` - golden section - 1.6180...
//!
//! The calculator does not have special type for boolean numbers. When using logical
//! operators any zero value is treated as `false` and `true` otherwise. So, doing
//! double NOT transforms any number into big integer `1` or `0` depending on if the
//! original value was zero

#[macro_use]
extern crate pest_derive;

pub mod errors;
pub mod parse;
pub mod stack;
pub mod value;
