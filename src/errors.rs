use num_bigint::BigInt;
use num_rational::BigRational;
use std::fmt;

#[derive(PartialEq)]
pub enum CalcError {
    None,

    StrToFloat(String),
    StrToInt(String),
    StrToRatio(String),
    IntToFloat(BigInt),
    RatioToFloat(BigRational),
    AngleToFloat(String),
    FloatToInt(f64),
    FloatToRatio(f64),
    DividedByZero(String),
    InvalidShift(String),

    NotForComplex(String),
    NotForNegativeInt(String),

    OnlyInt(String),

    NotSupportedYet(String, String),
    InvalidAgrument(String, String),
    ArgumentOutOfRange(String, String, String),

    EmptyValue,
    InvalidOp(String),
    TooManyOps,
    OpenBracketMismatch,
    ClosingBracketMismatch,
    FunctionUnfinished(String),
    FunctionNoArgs(String),
    FunctionNotEnoughArgs(String, usize),
    EmptyExpression,
    InsufficientOps,
    VarUndeclared(String),

    ParseFailed(String),

    Unreachable,
}

impl fmt::Display for CalcError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            CalcError::None => write!(f, "OK"),
            CalcError::StrToFloat(s) => write!(f, "Failed to convert '{}' to float", s),
            CalcError::StrToInt(s) => write!(f, "Failed to convert '{}' to integer", s),
            CalcError::StrToRatio(s) => write!(f, "Failed to convert '{}' to fraction", s),
            CalcError::AngleToFloat(s) => write!(f, "Failed to convert '{}' to angle", s),
            CalcError::IntToFloat(i) => write!(f, "Failed to convert integer {} to float", i),
            CalcError::RatioToFloat(r) => write!(f, "Failed to convert fraction {} to float", r),
            CalcError::FloatToInt(r) => write!(f, "Failed to convert float {} to integer", r),
            CalcError::FloatToRatio(r) => write!(f, "Failed to convert float {} to ratio", r),
            CalcError::DividedByZero(s) => write!(f, "'{}' divided by zero", s),
            CalcError::InvalidShift(s) => write!(f, "Cannot convert '{}' to usize", s),

            CalcError::NotForComplex(s) => write!(f, "Function '{}' is not supported for complex numbers", s),
            CalcError::NotForNegativeInt(s) => write!(f, "Function '{}' is not supported for negative integers", s),

            CalcError::OnlyInt(s) => write!(f, "{} supports only integers", s),

            CalcError::NotSupportedYet(func, typ) => {
                write!(f, "Function '{}' is not supported for {} numbers yet", func, typ)
            }
            CalcError::InvalidAgrument(func, val) => write!(f, "Invalid argument {} for function '{}'", func, val),
            CalcError::ArgumentOutOfRange(func, val, range) => {
                write!(f, "Argument {} of {} out of range({})", val, func, range)
            }

            CalcError::EmptyValue => write!(f, "Nor value neither operator found"),
            CalcError::InvalidOp(s) => write!(f, "Invalid operator '{}'", s),
            CalcError::TooManyOps => write!(f, "Too many operators"),
            CalcError::ClosingBracketMismatch => write!(f, "Mismatched closing bracket"),
            CalcError::OpenBracketMismatch => write!(f, "Mismatched opening bracket"),
            CalcError::FunctionUnfinished(s) => write!(f, "Closing bracket for function '{}' not found", s),
            CalcError::FunctionNoArgs(s) => write!(f, "Function '{}' requires an argument", s),
            CalcError::FunctionNotEnoughArgs(s, i) => write!(f, "Function '{}' requires at least {} arguments", s, i),
            CalcError::EmptyExpression => write!(f, "Nothing to calculate"),
            CalcError::InsufficientOps => write!(f, "Too many numbers"),

            CalcError::ParseFailed(s) => write!(f, "Failed to parse expression: {}", s),
            CalcError::VarUndeclared(s) => write!(f, "Variable '{}' not found", s),

            CalcError::Unreachable => write!(f, "unreachable"),
        }
    }
}

impl fmt::Debug for CalcError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            CalcError::None => write!(f, "OK"),
            CalcError::StrToFloat(s) => write!(f, "Failed to convert '{}' to float", s),
            CalcError::StrToInt(s) => write!(f, "Failed to convert '{}' to integer", s),
            CalcError::StrToRatio(s) => write!(f, "Failed to convert '{}' to fraction", s),
            CalcError::AngleToFloat(s) => write!(f, "Failed to convert '{}' to angle", s),
            CalcError::IntToFloat(i) => write!(f, "Failed to convert integer {} to float", i),
            CalcError::RatioToFloat(r) => write!(f, "Failed to convert fraction {} to float", r),
            CalcError::FloatToInt(r) => write!(f, "Failed to convert float {} to integer", r),
            CalcError::FloatToRatio(r) => write!(f, "Failed to convert float {} to ratio", r),
            CalcError::DividedByZero(s) => write!(f, "'{}' divided by zero", s),
            CalcError::InvalidShift(s) => write!(f, "Cannot convert '{}' to usize", s),

            CalcError::NotForComplex(s) => write!(f, "Function '{}' is not supported for complex numbers", s),
            CalcError::NotForNegativeInt(s) => write!(f, "Function '{}' is not supported for negative integers", s),

            CalcError::OnlyInt(s) => write!(f, "{} supports only integers", s),

            CalcError::NotSupportedYet(func, typ) => {
                write!(f, "Function '{}' is not supported for {} numbers yet", func, typ)
            }
            CalcError::InvalidAgrument(func, val) => write!(f, "Invalid argument {} for function '{}'", func, val),
            CalcError::ArgumentOutOfRange(func, val, range) => {
                write!(f, "Argument {} of {} out of range({})", val, func, range)
            }

            CalcError::EmptyValue => write!(f, "Nor value neither operator found"),
            CalcError::InvalidOp(s) => write!(f, "Invalid operator '{}'", s),
            CalcError::TooManyOps => write!(f, "Too many operators"),
            CalcError::ClosingBracketMismatch => write!(f, "Mismatched closing bracket"),
            CalcError::OpenBracketMismatch => write!(f, "Mismatched opening bracket"),
            CalcError::FunctionUnfinished(s) => write!(f, "Closing bracket for function '{}' not found", s),
            CalcError::FunctionNoArgs(s) => write!(f, "Function '{}' requires an argument", s),
            CalcError::FunctionNotEnoughArgs(s, i) => write!(f, "Function '{}' requires at least {} arguments", s, i),
            CalcError::EmptyExpression => write!(f, "Nothing to calculate"),
            CalcError::InsufficientOps => write!(f, "Too many numbers"),

            CalcError::ParseFailed(s) => write!(f, "Failed to parse expression: {}", s),
            CalcError::VarUndeclared(s) => write!(f, "Variable '{}' not found", s),

            CalcError::Unreachable => write!(f, "unreachable"),
        }
    }
}
