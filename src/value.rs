use dtoa;
use num_bigint::{BigInt, Sign};
use num_complex::Complex;
use num_rational::BigRational;
use num_traits::{FromPrimitive, Num, One, ToPrimitive, Zero};
use std::f64::{consts, EPSILON};
use std::fmt;
use std::str;

use crate::errors::*;

/// Expression calculation result: either value or error
pub type CalcResult = Result<Value, CalcError>;
pub(crate) type CalcErrorResult = Result<(), CalcError>;

/// Supported value types (Float is used for angles in degrees)
#[derive(Clone)]
pub enum Value {
    /// Big integer number
    Int(BigInt),
    /// Float number
    Float(f64),
    /// Rational number (numerator and denominator are big integers)
    Ratio(BigRational),
    /// Complex number
    Complex(Complex<f64>),
}

const F64_BUF_LEN: usize = 48;
fn format_f64(g: f64) -> String {
    let mut buf = [b'\0'; F64_BUF_LEN];
    match dtoa::write(&mut buf[..], g) {
        Ok(len) => match str::from_utf8(&buf[..len]) {
            Ok(s) => s.to_string(),
            Err(..) => format!("{}", g),
        },
        Err(..) => format!("{}", g),
    }
}

pub(crate) fn f64_equal(f1: f64, f2: f64) -> bool {
    (f1 - f2).abs() <= EPSILON
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            Value::Int(ref i) => write!(f, "{}", i),
            Value::Float(ref g) => write!(f, "{}", format_f64(*g)),
            Value::Ratio(ref r) => {
                let i = r.clone().to_integer();
                if i.is_zero() {
                    write!(f, "{}\\{}", r.numer(), r.denom())
                } else {
                    let mut rc = r.fract();
                    if rc < BigRational::zero() {
                        rc = -rc;
                    }
                    write!(f, "{}\\{}\\{}", i, rc.numer(), rc.denom())
                }
            }
            Value::Complex(ref c) => {
                if c.im >= 0.0 {
                    write!(f, "{}+{}i", format_f64(c.re), format_f64(c.im))
                } else {
                    write!(f, "{}{}i", format_f64(c.re), format_f64(c.im))
                }
            }
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            Value::Int(ref i) => write!(f, " Int({:?})", i),
            Value::Float(ref g) => write!(f, " Float({:?})", g),
            Value::Ratio(ref r) => write!(f, " Ratio({:?})", r),
            Value::Complex(ref c) => write!(f, " Complex({:?})", c),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, &other) {
            (Value::Int(ref i1), Value::Int(ref i2)) => i1 == i2,
            (Value::Float(ref f1), Value::Float(ref f2)) => f1 == f2,
            (Value::Ratio(ref r1), Value::Ratio(ref r2)) => r1 == r2,
            (Value::Complex(ref c1), Value::Complex(ref c2)) => c1 == c2,
            (_, _) => false,
        }
    }
}

fn int_to_f64(i: &BigInt) -> Result<f64, CalcError> {
    if let Some(f) = i.to_f64() {
        Ok(f)
    } else {
        Err(CalcError::IntToFloat(i.clone()))
    }
}

fn f64_to_int(f: f64) -> Result<BigInt, CalcError> {
    if let Some(i) = BigInt::from_f64(f) {
        Ok(i)
    } else {
        Err(CalcError::FloatToInt(f))
    }
}

fn f64_to_ratio(f: f64) -> Result<BigRational, CalcError> {
    if let Some(r) = BigRational::from_float(f) {
        Ok(r)
    } else {
        Err(CalcError::FloatToRatio(f))
    }
}

fn ratio_to_f64(r: &BigRational) -> Result<f64, CalcError> {
    if r.is_zero() {
        return Ok(0.0);
    }
    // extract the integer part first to avoid float overflow
    // in case of very long numer and denom
    let i = if let Some(f) = r.clone().to_integer().to_f64() {
        f
    } else {
        return Err(CalcError::RatioToFloat(r.clone()));
    };
    let r = r.fract();
    let n = if let Some(f) = r.numer().to_f64() {
        f
    } else {
        return Err(CalcError::RatioToFloat(r.clone()));
    };
    let d = if let Some(f) = r.denom().to_f64() {
        f
    } else {
        return Err(CalcError::RatioToFloat(r.clone()));
    };
    Ok(i + n / d)
}

fn str_to_bigint(s: &str) -> Result<BigInt, CalcError> {
    let s = s.replace("_", "");
    let s = s.replace(" ", "");
    let plen = "0x".len();
    if s.starts_with("0x") || s.starts_with("0X") {
        if let Ok(bi) = BigInt::from_str_radix(&s[plen..], 16) {
            return Ok(bi);
        }
        return Err(CalcError::StrToInt(s.to_owned()));
    } else if s.starts_with("0o") || s.starts_with("0O") {
        if let Ok(bi) = BigInt::from_str_radix(&s[plen..], 8) {
            return Ok(bi);
        }
        return Err(CalcError::StrToInt(s.to_owned()));
    } else if s.starts_with("0b") || s.starts_with("0B") {
        if let Ok(bi) = BigInt::from_str_radix(&s[plen..], 2) {
            return Ok(bi);
        }
        return Err(CalcError::StrToInt(s.to_owned()));
    }

    let pos = s.find(|c: char| c == 'e' || c == 'E').unwrap_or(0);
    if pos == 0 {
        if let Ok(i) = s.parse() {
            return Ok(i);
        } else {
            return Err(CalcError::StrToInt(s.to_owned()));
        }
    }
    let (s1, s2) = s.split_at(pos);
    let s2 = s2.trim_start_matches(|c| c == 'E' || c == 'e' || c == '+');

    let base = s1.parse();
    let pow = s2.parse();
    if base.is_err() || pow.is_err() {
        return Err(CalcError::StrToInt(s.to_owned()));
    }

    let mut base = base.unwrap();
    let pow = pow.unwrap();
    // TODO: fast power 10
    for _i in 0..pow {
        base *= 10;
    }
    Ok(base)
}

fn str_to_f64(s: &str) -> Result<f64, CalcError> {
    if let Ok(f) = s.parse::<f64>() {
        Ok(f)
    } else {
        Err(CalcError::StrToFloat(s.to_owned()))
    }
}

macro_rules! basic_op {
    ($id:ident, $op:tt, $cond:ident) => {
        pub fn $id(self, rhs: Value) -> CalcResult {
            match (&self, &rhs) {
                (Value::Complex(..), ..) | (.., Value::Complex(..)) => {
                    let c1 = self.into_raw_complex()?;
                    let c2 = rhs.into_raw_complex()?;
                    let c = Value::Complex(c1 $op c2);
                    if Value::is_like_int(&c) {
                        return Value::into_int(c);
                    }
                    Ok(c)
                },
                (Value::Float(..), ..) | (.., Value::Float(..)) => {
                    let f1 = self.into_raw_f64()?;
                    let f2 = rhs.into_raw_f64()?;
                    let f = Value::Float(f1 $op f2);
                    if Value::is_like_int(&f) {
                        return Value::into_int(f);
                    }
                    Ok(f)
                },
                (Value::Ratio(..), ..) | (.., Value::Ratio(..)) => {
                    let r1 = self.into_raw_ratio()?;
                    let r2 = rhs.into_raw_ratio()?;
                    let r = Value::Ratio(r1 $op r2);
                    if Value::is_like_int(&r) {
                        return Value::into_int(r);
                    }
                    Ok(r)
                },
                _ => {
                    let i1 = self.into_raw_big_int()?;
                    let i2 = rhs.into_raw_big_int()?;
                    if $cond {
                        if i1.clone() % i2.clone() == BigInt::zero() {
                            return Ok(Value::Int(i1 $op i2))
                        }
                        let f1 = i1.to_f64();
                        let f2 = i2.to_f64();
                        match (f1, f2) {
                            (Some(ff1), Some(ff2)) => {
                                Ok(Value::Float(ff1 / ff2))
                            },
                            (_, _) => {
                                Ok(Value::Int(i1 $op i2))
                            },
                        }
                    } else {
                        Ok(Value::Int(i1 $op i2))
                    }
                },
            }
        }
    }
}

macro_rules! div_op {
    ($id:ident, $op:tt, $cond:ident) => {
        pub fn $id(self, rhs: Value) -> CalcResult {
            if rhs.is_zero() {
                return Err(CalcError::DividedByZero(format!("{}", self)));
            }
            match (&self, &rhs) {
                (Value::Complex(..), ..) | (.., Value::Complex(..)) => {
                    let c2 = rhs.into_raw_complex()?;
                    let c1 = self.into_raw_complex()?;
                    let c = Value::Complex(c1 $op c2);
                    if Value::is_like_int(&c) {
                        return Value::into_int(c);
                    }
                    Ok(c)
                },
                (Value::Float(..), ..) | (.., Value::Float(..)) => {
                    let f2 = rhs.into_raw_f64()?;
                    let f1 = self.into_raw_f64()?;
                    let f = Value::Float(f1 $op f2);
                    if Value::is_like_int(&f) {
                        return Value::into_int(f);
                    }
                    Ok(f)
                },
                (Value::Ratio(..), ..) | (.., Value::Ratio(..)) => {
                    let r2 = rhs.into_raw_ratio()?;
                    let r1 = self.into_raw_ratio()?;
                    let r = Value::Ratio(r1 $op r2);
                    if Value::is_like_int(&r) {
                        return Value::into_int(r);
                    }
                    Ok(r)
                },
                _ => {
                    let i2 = rhs.into_raw_big_int()?;
                    let i1 = self.into_raw_big_int()?;
                    if $cond {
                        if i1.clone() % i2.clone() == BigInt::zero() {
                            return Ok(Value::Int(i1 $op i2))
                        }
                        let f1 = i1.to_f64();
                        let f2 = i2.to_f64();
                        match (f1, f2) {
                            (Some(ff1), Some(ff2)) => {
                                Ok(Value::Float(ff1 / ff2))
                            },
                            (_, _) => {
                                Ok(Value::Int(i1 $op i2))
                            },
                        }
                    } else {
                        Ok(Value::Int(i1 $op i2))
                    }
                },
            }
        }
    }
}

macro_rules! cmp_op {
    ($id:ident, $op:tt) => {
        pub fn $id(self, rhs: Value) -> CalcResult {
            match (&self, &rhs) {
                (Value::Complex(..), ..) | (.., Value::Complex(..)) => {
                    let c1 = self.into_raw_complex()?;
                    let c2 = rhs.into_raw_complex()?;
                    if c1.re $op c2.re && c1.im $op c2.im {
                        Ok(Value::Int(BigInt::one()))
                    } else {
                        Ok(Value::Int(BigInt::zero()))
                    }
                },
                (Value::Float(..), ..) | (.., Value::Float(..)) => {
                    let f1 = self.into_raw_f64()?;
                    let f2 = rhs.into_raw_f64()?;
                    if f1 $op f2 {
                        Ok(Value::Int(BigInt::one()))
                    } else {
                        Ok(Value::Int(BigInt::zero()))
                    }
                },
                (Value::Ratio(..), ..) | (.., Value::Ratio(..)) => {
                    let r1 = self.into_raw_ratio()?;
                    let r2 = rhs.into_raw_ratio()?;
                    if r1 $op r2 {
                        Ok(Value::Int(BigInt::one()))
                    } else {
                        Ok(Value::Int(BigInt::zero()))
                    }
                },
                _ => {
                    let i1 = self.into_raw_big_int()?;
                    let i2 = rhs.into_raw_big_int()?;
                    if i1 $op i2 {
                        Ok(Value::Int(BigInt::one()))
                    } else {
                        Ok(Value::Int(BigInt::zero()))
                    }
                },
            }
        }
    }
}
macro_rules! cmp_op_inv {
    ($id:ident, $idcall: ident, $op:tt) => {
        pub fn $id(self, rhs: Value) -> CalcResult {
            let res = self.$idcall(rhs)?;
            if res.is_zero() {
                Ok(Value::Int(BigInt::one()))
            } else {
                Ok(Value::Int(BigInt::zero()))
            }
        }
    };
}

macro_rules! round_op {
    ($id:ident) => {
        pub fn $id(self) -> CalcResult {
            match &self {
                Value::Complex(c) => {
                    let v = Value::Complex(Complex::new(c.re.$id(), c.im.$id()));
                    if Value::is_like_int(&v) {
                        let v = Value::into_int(v)?;
                        Ok(v)
                    } else {
                        Ok(v)
                    }
                }
                Value::Ratio(r) => {
                    let v = Value::Ratio(r.$id());
                    if Value::is_like_int(&v) {
                        let v = Value::into_int(v)?;
                        Ok(v)
                    } else {
                        Ok(v)
                    }
                }
                Value::Float(f) => {
                    let v = Value::Float(f.$id());
                    let v = Value::into_int(v)?;
                    Ok(v)
                }
                Value::Int(i) => Ok(Value::Int(i.clone())),
            }
        }
    };
}

macro_rules! bitwise_op {
    ($id:ident, $op:tt) => {
        pub fn $id(self, rhs: Value) -> CalcResult {
            match (&self, &rhs) {
                (Value::Int(i1), Value::Int(i2)) => {
                    let i1 = i1 $op i2;
                    Ok(Value::Int(i1))
                },
                _ => Err(CalcError::OnlyInt("bitwise operator".to_string())),
            }
        }
    }
}
macro_rules! bitwise_shift_op {
    ($id:ident, $op:tt) => {
        pub fn $id(self, rhs: Value) -> CalcResult {
            match (&self, &rhs) {
                (Value::Int(i1), Value::Int(i2)) => {
                    let shift = if let Some(us) = i2.clone().to_usize() {
                        us
                    } else {
                        return Err(CalcError::InvalidShift(format!("{}", i2)))
                    };
                    let i1 = i1 $op shift;
                    Ok(Value::Int(i1))
                },
                _ => Err(CalcError::OnlyInt("bitwise operator".to_string())),
            }
        }
    }
}

macro_rules! sin_cos {
    ($id:ident) => {
        pub fn $id(self) -> CalcResult {
            match &self {
                Value::Complex(c) => Ok(Value::Complex(c.$id())),
                Value::Float(f) => Ok(Value::Float(f.$id())),
                _ => {
                    let f = self.into_raw_f64()?;
                    Ok(Value::Float(f.$id()))
                },
            }
        }
    }
}
macro_rules! asin_cos {
    ($id:ident) => {
        pub fn $id(self) -> CalcResult {
            match &self {
                Value::Complex(c) => Ok(Value::Complex(c.$id())),
                _ => {
                    let f = self.into_raw_f64()?;
                    if f >= -1.0 && f <= 1.0 {
                        Ok(Value::Float(f.$id()))
                    } else {
                        let cm = Complex::new(f, 0.0);
                        Ok(Value::Complex(cm.$id()))
                    }
                }
            }
        }
    }
}

macro_rules! fn_hyper {
    ($id:ident) => {
        pub fn $id(self) -> CalcResult {
            match &self {
                Value::Complex(c) => Ok(Value::Complex(c.$id())),
                _ => {
                    let f = self.clone().into_raw_f64()?;
                    Ok(Value::Float(f.$id()))
                }
            }
        }
    }
}

impl Default for Value {
    fn default() -> Value {
        Value::Int(BigInt::zero())
    }
}

impl Value {
    pub fn new() -> Self {
        Default::default()
    }

    // --------------------------------

    pub(crate) fn into_int(self) -> CalcResult {
        match self {
            Value::Int(..) => Ok(self),
            Value::Float(f) => {
                let i = f64_to_int(f.floor())?;
                Ok(Value::Int(i))
            }
            Value::Ratio(r) => Ok(Value::Int(r.to_integer())),
            Value::Complex(c) => {
                let i = f64_to_int(c.re.floor())?;
                Ok(Value::Int(i))
            }
        }
    }

    pub(crate) fn into_float(self) -> CalcResult {
        match self {
            Value::Int(i) => {
                let f = int_to_f64(&i)?;
                Ok(Value::Float(f))
            }
            Value::Float(..) => Ok(self),
            Value::Ratio(r) => {
                let f = ratio_to_f64(&r)?;
                Ok(Value::Float(f))
            }
            Value::Complex(c) => Ok(Value::Float(c.re)),
        }
    }

    pub(crate) fn into_ratio(self) -> CalcResult {
        match self {
            Value::Ratio(..) => Ok(self),
            Value::Int(i) => Ok(Value::Ratio(BigRational::from_integer(i))),
            Value::Float(f) => {
                let r = f64_to_ratio(f)?;
                Ok(Value::Ratio(r))
            }
            Value::Complex(c) => {
                let r = f64_to_ratio(c.re)?;
                Ok(Value::Ratio(r))
            }
        }
    }

    pub(crate) fn into_complex(self) -> CalcResult {
        match self {
            Value::Complex(..) => Ok(self),
            Value::Float(f) => Ok(Value::Complex(Complex::new(f, 0.0))),
            Value::Int(i) => {
                let f = int_to_f64(&i)?;
                Ok(Value::Complex(Complex::new(f, 0.0)))
            }
            Value::Ratio(r) => {
                let f = ratio_to_f64(&r)?;
                Ok(Value::Complex(Complex::new(f, 0.0)))
            }
        }
    }

    //---------------------------------------------

    pub(crate) fn into_raw_f64(self) -> Result<f64, CalcError> {
        let v = Value::into_float(self)?;
        match v {
            Value::Float(f) => Ok(f),
            _ => Ok(0.0), // unreachable
        }
    }

    pub(crate) fn into_raw_big_int(self) -> Result<BigInt, CalcError> {
        let v = Value::into_int(self)?;
        match v {
            Value::Int(i) => Ok(i),
            _ => Ok(BigInt::zero()), // unreachable
        }
    }

    pub(crate) fn into_raw_ratio(self) -> Result<BigRational, CalcError> {
        let v = Value::into_ratio(self)?;
        match v {
            Value::Ratio(r) => Ok(r),
            _ => Ok(BigRational::zero()), // unreachable
        }
    }

    pub(crate) fn into_raw_complex(self) -> Result<Complex<f64>, CalcError> {
        let v = Value::into_complex(self)?;
        match v {
            Value::Complex(c) => Ok(c),
            _ => Ok(Complex::zero()), // unreachable
        }
    }

    //---------------------------------------------

    /// Convert &str to big integer number
    /// Supported formats:
    /// * Raw integer number - `1234`
    /// * Integer number and exponent (it must not include decimal point) - `12e2` = `1200`
    /// * Hexadecimal number - `0x12` or `0X12`
    /// * Octal number - `0o12` or `0O12`
    /// * Binary number - `0b101` or `0B101`
    ///
    /// For convenience digits can be separated with underscores:
    /// `3_00_1` is the same as `3001`
    pub fn from_str_integer(s: &str) -> CalcResult {
        let i = str_to_bigint(s)?;
        Ok(Value::Int(i))
    }

    /// Convert &str to float number
    /// Supported formats:
    /// * Without exponent - `1.023`
    /// * With exponent - `1.02e-5`
    ///
    /// Comma(,) can be used instead of decimal point(.):
    /// `1.25` is the same as `1,25`
    ///
    /// For convenience digits can be separated with underscores:
    /// `3_005.245_1` is the same as `3005.2451`
    pub fn from_str_float(s: &str) -> CalcResult {
        let s = s.replace("_", "");
        let s = s.replace(" ", "");
        let s = s.replace(',', ".");
        let f = str_to_f64(&s)?;
        Ok(Value::Float(f))
    }

    /// Convert &str to rational number
    /// Supported formats:
    /// * Numerator and denominator only: `1\2` = one half
    /// * With integer part: `3\1\2` = three and a half
    ///
    /// For convenience digits can be separated with underscores:
    /// `3_005\1_988` is the same as `3005\1988`
    pub fn from_str_ratio(st: &str) -> CalcResult {
        let s = st.replace("_", "");
        let s = s.replace(" ", "");
        let sp: Vec<&str> = s.splitn(3, '\\').collect();

        if sp.len() == 1 {
            return Self::from_str_integer(st);
        }

        let i = if sp.len() > 2 {
            str_to_bigint(sp[0])?
        } else {
            BigInt::zero()
        };
        let n = str_to_bigint(sp[sp.len() - 2])?;
        let d = str_to_bigint(sp[sp.len() - 1])?;

        if d.is_zero() {
            Ok(Value::Int(BigInt::zero()))
        } else {
            let d1 = d.clone();
            Ok(Value::Ratio(BigRational::new(i * d1 + n, d)))
        }
    }

    /// Convert &str that represents angle in degrees to float number
    /// Supported formats:
    /// * Full form with letters - `30d20m50s` - 30 degress, 20 angular minutes and 30 angular seconds
    /// * Full form with special characters - `30°20'50"`
    /// * Short form - degrees only - `30.25d` or `30.25°`
    ///
    /// Characters can be mixed: `30d20'50"`. Letters can be either lowercase or capital ones.
    ///
    /// Comma(,) can be used instead of decimal point(.):
    /// `1.25d` is the same as `1,25d`
    ///
    /// For convenience digits can be separated with underscores:
    /// `3_005.245_1d` is the same as `3005.2451d`
    pub fn from_str_angle(s: &str) -> CalcResult {
        let s = s.replace("_", "");
        let s = s.replace(",", ".");
        let parts: Vec<&str> = s
            .split(|c: char| {
                c == 'd'
                    || c == 'D'
                    || c == '°'
                    || c == 'm'
                    || c == 'M'
                    || c == '\''
                    || c == 's'
                    || c == 'S'
                    || c == '"'
            })
            .filter(|s| *s != "")
            .collect();

        let deg_ex = s.find(|c: char| c == 'd' || c == 'D' || c == '°').is_some();
        let min_ex = s.find(|c: char| c == 'm' || c == 'M' || c == '\'').is_some();
        let sec_ex = s.find(|c: char| c == 's' || c == 'S' || c == '"').is_some();
        let mut cnt = 0usize;
        if deg_ex {
            cnt += 1;
        }
        if min_ex {
            cnt += 1;
        }
        if sec_ex {
            cnt += 1;
        }
        if cnt > parts.len() {
            return Err(CalcError::AngleToFloat(s.to_owned()));
        }

        let mut deg = 0.0f64;
        let mut idx = 0;
        if deg_ex {
            deg = str_to_f64(parts[idx])?;
            idx += 1;
        }
        if min_ex {
            let min = str_to_f64(parts[idx])?;
            deg += min / 60.0;
            idx += 1;
        }
        if sec_ex {
            let sec = str_to_f64(parts[idx])?;
            deg += sec / 3600.0;
        }
        Ok(Value::Float(deg * consts::PI / 180.0))
    }

    /// Convert &str to complex number
    /// Supported formats:
    /// * "post" marker - `1+2i`
    /// * *pre" marker - `1+i2`
    ///
    /// `i` can be capital one. Instead of `i` letter `j` can be used.
    ///
    /// Note: while omitting real part is supported by this converter(e.g,
    /// it parses `2i` to `0+2i`), it is discouraged. Because a parser that
    /// parses the entire expression cannot detect such cases and may generate
    /// an error.
    ///
    /// Comma(,) can be used instead of decimal point(.):
    /// `1.25d` is the same as `1,25d`
    ///
    /// For convenience digits can be separated with underscores:
    /// `3_005.245_1d` is the same as `3005.2451d`
    pub fn from_str_complex(s: &str) -> CalcResult {
        let s = s.replace("_", "");
        let s = s.replace(",", ".");
        if let Some(pos) = s.find(|c: char| c == 'i' || c == 'I' || c == 'j' || c == 'J') {
            if pos == 0 {
                // only imaginary case: -i3.2e-5
                let f = str_to_f64(&s[pos + 1..])?;
                Ok(Value::Complex(Complex::new(0.0, f)))
            } else if pos == 1 {
                // imaginary and sign: -i3.2e-5
                let mut f = str_to_f64(&s[pos + 1..])?;
                if s.starts_with('-') {
                    f = -f
                }
                Ok(Value::Complex(Complex::new(0.0, f)))
            } else if pos == s.len() - 1 {
                // harder case: -2.1e-4-3.2-e5i
                let epos = s.rfind(|c: char| c == 'e' || c == 'E').unwrap_or_else(|| s.len());
                let mut spos = s.rfind(|c: char| c == '-' || c == '+').unwrap_or_else(|| s.len());
                if spos > epos {
                    // case when the imaginary number has 'e' power: '..-2.3e-4i'.
                    // need to look for the next '-' or '+' from the end
                    spos = s[..epos]
                        .rfind(|c: char| c == '-' || c == '+')
                        .unwrap_or_else(|| s.len());
                }
                if spos >= epos || spos == 0 {
                    let f = str_to_f64(&s[..s.len() - 1])?;
                    return Ok(Value::Complex(Complex::new(0.0, f)));
                }
                let r = str_to_f64(&s[..spos])?;
                let i = str_to_f64(&s[spos..s.len() - 1])?;
                Ok(Value::Complex(Complex::new(r, i)))
            } else {
                // easier case: -2.1e-4+i3.2e-5
                let r = str_to_f64(&s[..pos - 1])?;
                let mut i = str_to_f64(&s[pos + 1..])?;
                if &s[pos - 1..pos] == "-" {
                    i = -i;
                }
                Ok(Value::Complex(Complex::new(r, i)))
            }
        } else {
            let f = str_to_f64(&s)?;
            Ok(Value::Complex(Complex::new(f, 0.0)))
        }
    }

    //---------------------------------------------

    /// Returns true if the value is zero
    pub fn is_zero(&self) -> bool {
        match self {
            Value::Int(ref i) => i.is_zero(),
            Value::Float(ref f) => *f == 0.0,
            Value::Ratio(ref r) => r.is_zero(),
            Value::Complex(ref c) => c.is_zero(),
        }
    }

    // to check any value after any operation whether it can be converted
    // to BigInt
    fn is_like_int(&self) -> bool {
        match self {
            Value::Int(..) => true,
            Value::Float(f) => {
                let fa: f64 = f.abs();
                // f64 precision is about 19-20 digits,
                // so it is probable that any f64 > 1e20 is not precise
                fa >= 1.0 && fa < 1e22 && f64_equal(fa.floor(), fa)
            }
            Value::Ratio(ref r) => *r.denom() == BigInt::one(),
            Value::Complex(ref c) => {
                if c.im != 0.0 {
                    return false;
                }
                let fa: f64 = c.re.abs();
                fa >= 1.0 && fa < 1e22 && f64_equal(fa.floor(), fa)
            }
        }
    }

    basic_op!(addition, +, false);
    basic_op!(subtract, -, false);
    basic_op!(multiply, *, false);

    div_op!(divide, /, true);
    div_op!(reminder, %, false);

    /// Divides and truncates the result.
    /// Note: the result is always big integer number even if
    /// two complex numbers are divided. It means in that the result for
    /// complex numbers may be incorrect or strange
    pub fn div_int(self, rhs: Value) -> CalcResult {
        if rhs.is_zero() {
            return Err(CalcError::DividedByZero(format!("{}", self)));
        }
        match (&self, &rhs) {
            (Value::Complex(..), ..) | (.., Value::Complex(..)) => {
                let c2 = rhs.into_raw_complex()?;
                let c1 = self.into_raw_complex()?;
                let c = Value::Complex(c1 / c2);
                Value::into_int(c)
            }
            (Value::Float(..), ..) | (.., Value::Float(..)) => {
                let f2 = rhs.into_raw_f64()?;
                let f1 = self.into_raw_f64()?;
                let f = Value::Float(f1 / f2);
                Value::into_int(f)
            }
            (Value::Ratio(..), ..) | (.., Value::Ratio(..)) => {
                let r2 = rhs.into_raw_ratio()?;
                let r1 = self.into_raw_ratio()?;
                let r = Value::Ratio(r1 / r2);
                Value::into_int(r)
            }
            _ => {
                let i2 = rhs.into_raw_big_int()?;
                let i1 = self.into_raw_big_int()?;
                Ok(Value::Int(i1 / i2))
            }
        }
    }

    /// Inverts the sign of the value
    pub fn negate(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Complex(-c)),
            Value::Ratio(r) => Ok(Value::Ratio(-r)),
            Value::Float(f) => Ok(Value::Float(-f)),
            Value::Int(i) => Ok(Value::Int(-i)),
        }
    }

    /// Calculates modulus of a complex number
    pub fn norm(self) -> CalcResult {
        let v = Value::into_complex(self)?;
        match &v {
            Value::Complex(c) => Ok(Value::Float(c.norm())),
            _ => Err(CalcError::Unreachable),
        }
    }

    /// Conjugates a complex number
    pub fn conj(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Complex(c.conj())),
            _ => Ok(self),
        }
    }

    /// Returns imaginary part of a complex number
    pub fn im(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Float(c.im)),
            _ => Ok(Value::Float(0.0)),
        }
    }

    /// Returns real part of a complex number
    pub fn re(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Float(c.re)),
            _ => Ok(self),
        }
    }

    cmp_op!(eq, ==);
    cmp_op!(less, <);
    cmp_op!(lesseq, <=);
    cmp_op_inv!(neq, eq, !=);
    cmp_op_inv!(greater, lesseq, >);
    cmp_op_inv!(greatereq, less, >=);

    /// Inverts value as if it is a boolean one.
    /// Since the library does not have dedicated type for boolean values,
    /// big integers play their role. Rules of inversion:
    /// * Any zero value -> `1`
    /// * `0` in all other cases
    pub fn logical_not(self) -> CalcResult {
        if self.is_zero() {
            Ok(Value::Int(BigInt::one()))
        } else {
            Ok(Value::Int(BigInt::zero()))
        }
    }

    pub fn logical_and(self, rhs: Value) -> CalcResult {
        if self.is_zero() || rhs.is_zero() {
            Ok(Value::Int(BigInt::zero()))
        } else {
            Ok(Value::Int(BigInt::one()))
        }
    }

    pub fn logical_or(self, rhs: Value) -> CalcResult {
        if self.is_zero() && rhs.is_zero() {
            Ok(Value::Int(BigInt::zero()))
        } else {
            Ok(Value::Int(BigInt::one()))
        }
    }

    /// Extract fractional part of a float number
    pub fn fract(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Complex(Complex::new(c.re.fract(), c.im.fract()))),
            Value::Ratio(r) => Ok(Value::Ratio(r.fract())),
            Value::Float(f) => Ok(Value::Float(f.fract())),
            Value::Int(..) => Ok(Value::Int(BigInt::zero())),
        }
    }

    /// Returns absolute value of a number
    /// For complex numbers only its real part changes
    pub fn abs(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Complex(Complex::new(c.re.abs(), c.im))),
            Value::Ratio(r) => {
                if *r < BigRational::zero() {
                    Ok(Value::Ratio(-r))
                } else {
                    Ok(Value::Ratio(r.clone()))
                }
            }
            Value::Float(f) => Ok(Value::Float(f.abs())),
            Value::Int(i) => {
                if *i < BigInt::zero() {
                    Ok(Value::Int(-i))
                } else {
                    Ok(Value::Int(i.clone()))
                }
            }
        }
    }

    round_op!(floor);
    round_op!(ceil);
    round_op!(round);
    round_op!(trunc);

    /// Squares the value.
    /// Automatically converts complex number into float one if imaginary part
    /// of the result is zero
    pub fn sqr(self) -> CalcResult {
        match &self {
            Value::Complex(c) => {
                let c = c * c;
                if c.im == 0.0 {
                    Ok(Value::Float(c.re))
                } else {
                    Ok(Value::Complex(c))
                }
            }
            Value::Ratio(r) => Ok(Value::Ratio(r * r)),
            Value::Float(f) => Ok(Value::Float(f * f)),
            Value::Int(i) => Ok(Value::Int(i * i)),
        }
    }

    /// Returns sign of the number (for complex number it is a sign of real part):
    /// * `1` for a number greater than `0`
    /// * `0` for zero number
    /// * `-1` for number less than `0`
    pub fn signum(self) -> CalcResult {
        match &self {
            Value::Complex(c) => {
                if c.re == 0.0 {
                    Ok(Value::Int(BigInt::zero()))
                } else if c.re > 0.0 {
                    Ok(Value::Int(BigInt::one()))
                } else {
                    Ok(Value::Int(-BigInt::one()))
                }
            }
            Value::Ratio(r) => {
                if r.is_zero() {
                    Ok(Value::Int(BigInt::zero()))
                } else if *r > BigRational::zero() {
                    Ok(Value::Int(BigInt::one()))
                } else {
                    Ok(Value::Int(-BigInt::one()))
                }
            }
            Value::Float(f) => {
                if *f == 0.0 {
                    Ok(Value::Int(BigInt::zero()))
                } else if *f > 0.0 {
                    Ok(Value::Int(BigInt::one()))
                } else {
                    Ok(Value::Int(-BigInt::one()))
                }
            }
            Value::Int(i) => {
                if i.is_zero() {
                    Ok(Value::Int(BigInt::zero()))
                } else if *i > BigInt::zero() {
                    Ok(Value::Int(BigInt::one()))
                } else {
                    Ok(Value::Int(-BigInt::one()))
                }
            }
        }
    }

    /// Returns square root of a number.
    /// Automatically converts a negative number into complex one before calculation
    pub fn sqrt(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Complex(c.sqrt())),
            Value::Ratio(r) => {
                let f = ratio_to_f64(r)?;
                if f >= 0.0 {
                    Ok(Value::Float(f.sqrt()))
                } else {
                    let f = -f;
                    let c = Complex::new(0.0, f.sqrt());
                    Ok(Value::Complex(c))
                }
            }
            Value::Float(f) => {
                if *f >= 0.0 {
                    Ok(Value::Float(f.sqrt()))
                } else {
                    let f = -f;
                    let c = Complex::new(0.0, f.sqrt());
                    Ok(Value::Complex(c))
                }
            }
            Value::Int(i) => {
                if *i < BigInt::zero() {
                    let i = -i;
                    let f = int_to_f64(&i)?;
                    Ok(Value::Complex(Complex::new(0.0, f.sqrt())))
                } else {
                    let sq = i.sqrt();
                    if sq.clone() * sq.clone() == *i {
                        Ok(Value::Int(sq))
                    } else {
                        let f = int_to_f64(i)?;
                        Ok(Value::Float(f.sqrt()))
                    }
                }
            }
        }
    }

    /// Returns cubic root of a number.
    pub fn cbrt(self) -> CalcResult {
        match &self {
            Value::Complex(..) => self.power(Value::Float(1.0f64 / 3.0f64)),
            Value::Ratio(r) => {
                let f = ratio_to_f64(r)?;
                Ok(Value::Float(f.cbrt()))
            }
            Value::Float(f) => Ok(Value::Float(f.cbrt())),
            Value::Int(i) => {
                let cb = i.cbrt();
                if cb.clone() * cb.clone() * cb.clone() == *i {
                    return Ok(Value::Int(cb));
                }
                let f = int_to_f64(&i)?;
                Ok(Value::Float(f.cbrt()))
            }
        }
    }

    fn fast_power(self, pow: BigInt) -> CalcResult {
        if pow.is_zero() {
            return Ok(Value::Int(BigInt::one()));
        }
        let mut pow = pow;
        let mut inv = false;
        let sgn = pow.sign();
        if sgn == Sign::Minus {
            inv = true;
            pow = -pow;
        }

        let mut res = Value::Int(BigInt::one());
        let mut base = self;
        while pow > BigInt::zero() {
            if pow.clone() % BigInt::from(2) == BigInt::zero() {
                pow /= BigInt::from(2);
                base = base.clone().multiply(base.clone())?;
            } else {
                pow -= BigInt::one();
                res = res.multiply(base.clone())?;
            }
        }
        if inv {
            return Value::Int(BigInt::one()).divide(res);
        }
        if Value::is_like_int(&res) {
            res = Value::into_int(res)?
        }
        Ok(res)
    }

    /// Raises a number into arbitrary power.
    /// Automatic conversion as `sqrt` does is not not supported yet.
    /// For integer power degrees the fast and accurate algorithm is used.
    /// For float degrees the power is calculated using `exp`
    pub fn power(self, rhs: Value) -> CalcResult {
        match (&self, &rhs) {
            (Value::Complex(..), ..) | (.., Value::Complex(..)) => {
                let v = self.into_raw_complex()?;
                let pow = rhs.into_raw_complex()?;
                Ok(Value::Complex(v.powc(pow)))
            }
            (.., Value::Float(..)) => {
                let f1 = self.into_raw_f64()?;
                let f2 = rhs.into_raw_f64()?;
                let f1 = Value::Float(f1.powf(f2));
                if Value::is_like_int(&f1) {
                    return Value::into_int(f1);
                }
                Ok(f1)
            }
            (.., Value::Int(i)) => self.fast_power(i.clone()),
            _ => Err(CalcError::Unreachable),
        }
    }

    /// Returns factorial of a number.
    /// Complex numbers generates an error.
    /// Calculation factorial of negative or float number using gamma function
    /// is not supported yet
    pub fn fact(self) -> CalcResult {
        if Value::is_zero(&self) {
            return Ok(Value::Int(BigInt::one()));
        }

        match &self {
            Value::Complex(..) => Err(CalcError::NotForComplex("factorial".to_owned())),
            Value::Ratio(..) | Value::Float(..) => {
                if Value::is_like_int(&self) {
                    let i = Value::into_int(self)?;
                    let i = if let Value::Int(i1) = i {
                        i1
                    } else {
                        return Err(CalcError::Unreachable);
                    };
                    if i < BigInt::zero() {
                        return Err(CalcError::NotForNegativeInt("factorial".to_owned()));
                    }
                    let mut res = BigInt::one();
                    let mut cnt = BigInt::from(1);
                    while cnt <= i {
                        res *= cnt.clone();
                        cnt += BigInt::one();
                    }
                    return Ok(Value::Int(res));
                }
                // TODO: use gamma function
                Err(CalcError::NotSupportedYet("factorial".to_owned(), "float".to_owned()))
            }
            Value::Int(i) => {
                if *i < BigInt::zero() {
                    return Err(CalcError::NotForNegativeInt("factorial".to_owned()));
                }
                let mut res = BigInt::one();
                let mut cnt = BigInt::from(1);
                while cnt <= *i {
                    res *= cnt.clone();
                    cnt += BigInt::one();
                }
                Ok(Value::Int(res))
            }
        }
    }

    bitwise_op!(bit_or, |);
    bitwise_op!(bit_and, &);
    bitwise_op!(bit_xor, ^);
    bitwise_shift_op!(bit_shl, <<);
    bitwise_shift_op!(bit_shr, >>);

    pub fn bit_not(self) -> CalcResult {
        match &self {
            Value::Int(i1) => Ok(Value::Int(!i1)),
            _ => Err(CalcError::OnlyInt("bitwise not".to_string())),
        }
    }

    sin_cos!(sin);
    sin_cos!(cos);
    pub fn tan(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Complex(c.tan())),
            _ => {
                let f = self.clone().into_raw_f64()?;
                let half = consts::PI / 2.0;
                let ipart = (f / half).trunc();
                if f64_equal(ipart * half, f) {
                    Err(CalcError::InvalidAgrument("tan".to_owned(), format!("{}", self)))
                } else {
                    Ok(Value::Float(f.tan()))
                }
            }
        }
    }

    asin_cos!(asin);
    asin_cos!(acos);
    pub fn atan(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Complex(c.atan())),
            _ => {
                let f = self.into_raw_f64()?;
                Ok(Value::Float(f.atan()))
            }
        }
    }

    fn_hyper!(sinh);
    fn_hyper!(cosh);
    fn_hyper!(tanh);
    fn_hyper!(asinh);
    fn_hyper!(acosh);
    fn_hyper!(exp);
    pub fn atanh(self) -> CalcResult {
        match &self {
            Value::Complex(c) => Ok(Value::Complex(c.atanh())),
            _ => {
                let f = self.clone().into_raw_f64()?;
                if f >= -1.0 && f <= 1.0 {
                    Ok(Value::Float(f.atanh()))
                } else {
                    Err(CalcError::InvalidAgrument("atanh".to_owned(), format!("{}", self)))
                }
            }
        }
    }

    /// Returns natural logarithm of a number.
    /// Automatically converts a negative number to a complex one before calculation
    pub fn ln(self) -> CalcResult {
        if Value::is_zero(&self) {
            return Err(CalcError::InvalidAgrument("ln".to_owned(), format!("{}", self)));
        }
        match &self {
            Value::Complex(c) => Ok(Value::Complex(c.ln())),
            _ => {
                let f = self.clone().into_raw_f64()?;
                if f > 0.0 {
                    Ok(Value::Float(f.ln()))
                } else {
                    let cm = Complex::new(f, 0.0);
                    Ok(Value::Complex(cm.ln()))
                }
            }
        }
    }

    /// Converts float or integer number into rational one.
    /// Complex numbers generate an error
    pub fn ratio(self) -> CalcResult {
        match &self {
            Value::Ratio(..) => Ok(self),
            Value::Int(i) => Ok(Value::Ratio(BigRational::new(i.clone(), BigInt::one()))),
            Value::Float(f) => {
                if let Some(r) = BigRational::from_float(*f) {
                    Ok(Value::Ratio(r))
                } else {
                    Err(CalcError::InvalidAgrument("ratio".to_owned(), format!("{}", f)))
                }
            }
            Value::Complex(..) => Err(CalcError::NotForComplex("ratio".to_string())),
        }
    }

    /// Greatest common divisor
    pub fn gcd(self, rhs: Value) -> CalcResult {
        let mut v1 = self.into_raw_big_int()?;
        let mut v2 = rhs.into_raw_big_int()?;
        if v1 < BigInt::zero() {
            v1 = -v1;
        }
        if v2 < BigInt::zero() {
            v2 = -v2;
        }

        loop {
            if v1.is_zero() {
                return Ok(Value::Int(v2));
            }
            if v2.is_zero() {
                return Ok(Value::Int(v1));
            }
            if v1 < v2 {
                std::mem::swap(&mut v1, &mut v2);
            }

            let m = v1 % v2.clone();
            v1 = v2;
            v2 = m;
        }
    }

    /// Least Common Multiple
    pub fn lcm(self, rhs: Value) -> CalcResult {
        let gcd = self.clone().gcd(rhs.clone())?;
        let gcd = gcd.into_raw_big_int()?;
        let mut v1 = self.into_raw_big_int()?;
        let mut v2 = rhs.into_raw_big_int()?;
        if v1 < BigInt::zero() {
            v1 = -v1;
        }
        if v2 < BigInt::zero() {
            v2 = -v2;
        }

        Ok(Value::Int(v1 / gcd * v2))
    }

    /// Is Value a prime number. Returns error if a value is not integer
    /// Naive and slow algorithm for large integers
    pub fn is_prime(self) -> CalcResult {
        let v = self.abs()?;
        let v = if let Value::Int(i) = v {
            i
        } else {
            return Err(CalcError::OnlyInt("is_prime".to_string()));
        };

        let res = if v <= BigInt::one() {
            Value::Int(BigInt::zero())
        } else if v > BigInt::one() && v < BigInt::from(4) {
            Value::Int(BigInt::one())
        } else {
            if v.clone() % BigInt::from(2) == BigInt::zero() {
                Value::Int(BigInt::zero())
            } else {
                let upto = v.clone().sqrt();
                let mut curr = BigInt::from(3);
                let mut r = BigInt::one();
                while curr <= upto {
                    if v.clone() % curr.clone() == BigInt::zero() {
                        r = BigInt::zero();
                        break;
                    }
                    curr = curr + BigInt::from(2);
                }
                Value::Int(r)
            }
        };
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::f64::consts;
    #[test]
    fn test_int_str() {
        let v = Value::from_str_integer("10002");
        assert_eq!(v, Ok(Value::Int(BigInt::from(10002i64))));
        let v = Value::from_str_integer("10_00_2");
        assert_eq!(v, Ok(Value::Int(BigInt::from(10002i64))));
        let v = Value::from_str_integer("-10002");
        assert_eq!(v, Ok(Value::Int(BigInt::from(-10002i64))));
        let v = Value::from_str_integer("33e5");
        assert_eq!(v, Ok(Value::Int(BigInt::from(3300000i64))));
        let v = Value::from_str_integer("33E6");
        assert_eq!(v, Ok(Value::Int(BigInt::from(33000000i64))));

        let v = Value::from_str_integer("0Xff");
        assert_eq!(v, Ok(Value::Int(BigInt::from(255i64))));
        let v = Value::from_str_integer("0xff");
        assert_eq!(v, Ok(Value::Int(BigInt::from(255i64))));
        let v = Value::from_str_integer("0O33");
        assert_eq!(v, Ok(Value::Int(BigInt::from(27i64))));
        let v = Value::from_str_integer("0o33");
        assert_eq!(v, Ok(Value::Int(BigInt::from(27i64))));
        let v = Value::from_str_integer("0B101");
        assert_eq!(v, Ok(Value::Int(BigInt::from(5i64))));
        let v = Value::from_str_integer("0b101");
        assert_eq!(v, Ok(Value::Int(BigInt::from(5i64))));
    }
    #[test]
    fn test_float_str() {
        let v = Value::from_str_float("10002");
        assert_eq!(v, Ok(Value::Float(10002.0f64)));
        let v = Value::from_str_float("10_00_2");
        assert_eq!(v, Ok(Value::Float(10002.0f64)));
        let v = Value::from_str_float("10_00_3.5");
        assert_eq!(v, Ok(Value::Float(10003.5f64)));
        let v = Value::from_str_float("10_00_3,5");
        assert_eq!(v, Ok(Value::Float(10003.5f64)));
        let v = Value::from_str_float("1.0002e5");
        assert_eq!(v, Ok(Value::Float(100020.0f64)));
        let v = Value::from_str_float("200e-2");
        assert_eq!(v, Ok(Value::Float(2.0f64)));
    }
    #[test]
    fn test_ratio_str() {
        let v = Value::from_str_ratio("1\\2");
        assert_eq!(v, Ok(Value::Ratio(BigRational::new(BigInt::one(), BigInt::from(2i64)))));
        let v = Value::from_str_ratio("3\\2\\10");
        assert_eq!(
            v,
            Ok(Value::Ratio(BigRational::new(
                BigInt::from(3i64 * 10i64 + 2i64),
                BigInt::from(10i64)
            )))
        );
    }
    #[test]
    fn test_angle_str() {
        let coef: f64 = consts::PI / 180.0f64;
        let v = Value::from_str_angle("10d");
        assert_eq!(v, Ok(Value::Float(10f64 * coef)));
        let v = Value::from_str_angle("10°");
        assert_eq!(v, Ok(Value::Float(10f64 * coef)));
        let v = Value::from_str_angle("10.5d");
        assert_eq!(v, Ok(Value::Float(10.5f64 * coef)));
        let v = Value::from_str_angle("10d30m");
        assert_eq!(v, Ok(Value::Float(10.5f64 * coef)));
        let v = Value::from_str_angle("10d30m900s");
        assert_eq!(v, Ok(Value::Float(10.75f64 * consts::PI / 180.0f64)));
    }
    #[test]
    fn test_complex_str() {
        let v = Value::from_str_complex("10.0e-1+50e-3i");
        assert_eq!(v, Ok(Value::Complex(Complex::new(1.0f64, 0.05f64))));
        let v = Value::from_str_complex("10.0e1-50e2i");
        assert_eq!(v, Ok(Value::Complex(Complex::new(100.0f64, -5000.0f64))));
        let v = Value::from_str_complex("10.0e-1+50e-3j");
        assert_eq!(v, Ok(Value::Complex(Complex::new(1.0f64, 0.05f64))));
        let v = Value::from_str_complex("10.0e-1+50e-3I");
        assert_eq!(v, Ok(Value::Complex(Complex::new(1.0f64, 0.05f64))));
        let v = Value::from_str_complex("10.0e-1+50e-3J");
        assert_eq!(v, Ok(Value::Complex(Complex::new(1.0f64, 0.05f64))));

        let v = Value::from_str_complex("10.0e-1-i50e-3");
        assert_eq!(v, Ok(Value::Complex(Complex::new(1.0f64, -0.05f64))));
        let v = Value::from_str_complex("10.0e1-i50e2");
        assert_eq!(v, Ok(Value::Complex(Complex::new(100.0f64, -5000.0f64))));
        let v = Value::from_str_complex("10.0e-1-j50e-3");
        assert_eq!(v, Ok(Value::Complex(Complex::new(1.0f64, -0.05f64))));
        let v = Value::from_str_complex("10.0e-1-I50e-3");
        assert_eq!(v, Ok(Value::Complex(Complex::new(1.0f64, -0.05f64))));
        let v = Value::from_str_complex("10.0e-1-J50e-3");
        assert_eq!(v, Ok(Value::Complex(Complex::new(1.0f64, -0.05f64))));
        let v = Value::from_str_complex("-10.0e-1-J50e-3");
        assert_eq!(v, Ok(Value::Complex(Complex::new(-1.0f64, -0.05f64))));

        let v = Value::from_str_complex("-i50e-3");
        assert_eq!(v, Ok(Value::Complex(Complex::new(0.0f64, -0.05f64))));
        let v = Value::from_str_complex("j50e-3");
        assert_eq!(v, Ok(Value::Complex(Complex::new(0.0f64, 0.05f64))));
        let v = Value::from_str_complex("-50e-3J");
        assert_eq!(v, Ok(Value::Complex(Complex::new(0.0f64, -0.05f64))));
        let v = Value::from_str_complex("50e-3I");
        assert_eq!(v, Ok(Value::Complex(Complex::new(0.0f64, 0.05f64))));
        let v = Value::from_str_complex("-i50e3");
        assert_eq!(v, Ok(Value::Complex(Complex::new(0.0f64, -50000.0f64))));
        let v = Value::from_str_complex("j50e3");
        assert_eq!(v, Ok(Value::Complex(Complex::new(0.0f64, 50000.0f64))));
        let v = Value::from_str_complex("-50e3J");
        assert_eq!(v, Ok(Value::Complex(Complex::new(0.0f64, -50000.0f64))));
        let v = Value::from_str_complex("50e3I");
        assert_eq!(v, Ok(Value::Complex(Complex::new(0.0f64, 50000.0f64))));
    }
    #[test]
    fn test_to_str() {
        let v = Value::Int(BigInt::from(12345));
        assert_eq!(v.to_string(), "12345");
        let v = Value::Float(2.25f64);
        assert_eq!(v.to_string(), "2.25");
        let v = Value::Ratio(BigRational::new(BigInt::from(23), BigInt::from(35)));
        assert_eq!(v.to_string(), "23\\35");
        let v = Value::Ratio(BigRational::new(BigInt::from(23), BigInt::from(5)));
        assert_eq!(v.to_string(), "4\\3\\5");
        let v = Value::Complex(Complex::new(0.0, 1.25));
        assert_eq!(v.to_string(), "0.0+1.25i");
        let v = Value::Complex(Complex::new(4.5, -3.25));
        assert_eq!(v.to_string(), "4.5-3.25i");
    }
    #[test]
    fn test_convert_int() {
        let v = Value::Int(BigInt::from(123));
        let f = Value::into_float(v.clone());
        assert_eq!(f, Ok(Value::Float(123.0)));
        let f = Value::into_complex(v.clone());
        assert_eq!(f, Ok(Value::Complex(Complex::new(123.0, 0.0))));
        let f = Value::into_ratio(v.clone());
        assert_eq!(f, Ok(Value::Ratio(BigRational::new(BigInt::from(123), BigInt::one()))));
    }
    #[test]
    fn test_convert_float() {
        let v = Value::Float(12.5);
        let f = Value::into_int(v.clone());
        assert_eq!(f, Ok(Value::Int(BigInt::from(12))));
        let f = Value::into_complex(v.clone());
        assert_eq!(f, Ok(Value::Complex(Complex::new(12.5, 0.0))));
        let f = Value::into_ratio(v.clone());
        assert_eq!(f, Ok(Value::Ratio(BigRational::new(BigInt::from(25), BigInt::from(2)))));
    }
    #[test]
    fn test_convert_ratio() {
        let v = Value::Ratio(BigRational::new(BigInt::from(5), BigInt::from(2)));
        let f = Value::into_int(v.clone());
        assert_eq!(f, Ok(Value::Int(BigInt::from(2))));
        let f = Value::into_complex(v.clone());
        assert_eq!(f, Ok(Value::Complex(Complex::new(2.5, 0.0))));
        let f = Value::into_float(v.clone());
        assert_eq!(f, Ok(Value::Float(2.5)));
    }
    #[test]
    fn test_convert_complex() {
        let v = Value::Complex(Complex::new(2.5, 3.5));
        let f = Value::into_int(v.clone());
        assert_eq!(f, Ok(Value::Int(BigInt::from(2))));
        let f = Value::into_ratio(v.clone());
        assert_eq!(f, Ok(Value::Ratio(BigRational::new(BigInt::from(5), BigInt::from(2)))));
        let f = Value::into_float(v.clone());
        assert_eq!(f, Ok(Value::Float(2.5)));
    }
    #[test]
    fn test_add() {
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Int(BigInt::from(4));
        let r = v1.addition(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::from(7))));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Float(4.5);
        let r = v1.addition(v2);
        assert_eq!(r, Ok(Value::Float(7.5)));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Ratio(BigRational::new(BigInt::from(4), BigInt::from(5)));
        let r = v1.addition(v2);
        assert_eq!(r, Ok(Value::Ratio(BigRational::new(BigInt::from(19), BigInt::from(5)))));
        let v1 = Value::Float(0.5);
        let v2 = Value::Complex(Complex::new(4.5, 5.0));
        let r = v1.addition(v2);
        assert_eq!(r, Ok(Value::Complex(Complex::new(5.0, 5.0))));
    }
    #[test]
    fn test_sub() {
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Int(BigInt::from(4));
        let r = v1.subtract(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::from(-1))));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Float(4.5);
        let r = v1.subtract(v2);
        assert_eq!(r, Ok(Value::Float(-1.5)));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Ratio(BigRational::new(BigInt::from(4), BigInt::from(5)));
        let r = v1.subtract(v2);
        assert_eq!(r, Ok(Value::Ratio(BigRational::new(BigInt::from(11), BigInt::from(5)))));
        let v1 = Value::Float(0.5);
        let v2 = Value::Complex(Complex::new(4.5, 5.0));
        let r = v1.subtract(v2);
        assert_eq!(r, Ok(Value::Complex(Complex::new(-4.0, -5.0))));
    }
    #[test]
    fn test_mul() {
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Int(BigInt::from(4));
        let r = v1.multiply(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::from(12))));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Float(4.5);
        let r = v1.multiply(v2);
        assert_eq!(r, Ok(Value::Float(13.5)));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Ratio(BigRational::new(BigInt::from(4), BigInt::from(5)));
        let r = v1.multiply(v2);
        assert_eq!(r, Ok(Value::Ratio(BigRational::new(BigInt::from(12), BigInt::from(5)))));
        let v1 = Value::Float(5.0);
        let v2 = Value::Complex(Complex::new(4.0, 1.0));
        let r = v1.multiply(v2);
        assert_eq!(r, Ok(Value::Complex(Complex::new(20.0, 5.0))));
    }
    #[test]
    fn test_div() {
        let v1 = Value::Int(BigInt::from(12));
        let v2 = Value::Int(BigInt::from(4));
        let r = v1.divide(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::from(3))));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Int(BigInt::from(4));
        let r = v1.divide(v2);
        assert_eq!(r, Ok(Value::Float(0.75)));
        let v1 = Value::Float(3.0);
        let v2 = Value::Float(1.5);
        let r = v1.divide(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::from(2))));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Ratio(BigRational::new(BigInt::from(4), BigInt::from(5)));
        let r = v1.divide(v2);
        assert_eq!(r, Ok(Value::Ratio(BigRational::new(BigInt::from(15), BigInt::from(4)))));
        let v1 = Value::Float(5.0);
        let v2 = Value::Complex(Complex::new(5.0, 5.0));
        let r = v1.divide(v2);
        assert_eq!(r, Ok(Value::Complex(Complex::new(0.5, -0.5))));
    }
    #[test]
    fn test_div_int() {
        let v1 = Value::Int(BigInt::from(12));
        let v2 = Value::Int(BigInt::from(4));
        let r = v1.div_int(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::from(3))));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Int(BigInt::from(4));
        let r = v1.div_int(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::zero())));
        let v1 = Value::Float(3.0);
        let v2 = Value::Float(1.5);
        let r = v1.div_int(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::from(2))));
        let v1 = Value::Float(5.0);
        let v2 = Value::Float(3.0);
        let r = v1.div_int(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::one())));
        let v1 = Value::Int(BigInt::from(3));
        let v2 = Value::Ratio(BigRational::new(BigInt::from(4), BigInt::from(5)));
        let r = v1.div_int(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::from(3))));
        let v1 = Value::Complex(Complex::new(50.0, 25.0));
        let v2 = Value::Float(5.0);
        let r = v1.div_int(v2);
        assert_eq!(r, Ok(Value::Int(BigInt::from(10))));
    }
    #[test]
    fn test_neg() {
        let v = Value::Int(BigInt::from(12)).negate();
        assert_eq!(v, Ok(Value::Int(BigInt::from(-12))));
        let v = Value::Float(3.4).negate();
        assert_eq!(v, Ok(Value::Float(-3.4)));
        let v = Value::Ratio(BigRational::new(BigInt::from(2), BigInt::from(5))).negate();
        assert_eq!(v, Ok(Value::Ratio(-BigRational::new(BigInt::from(2), BigInt::from(5)))));
        let v = Value::Complex(Complex::new(3.0, 4.0)).negate();
        assert_eq!(v, Ok(Value::Complex(Complex::new(-3.0, -4.0))));
    }
    #[test]
    fn test_conj() {
        let v = Value::Float(3.4).conj();
        assert_eq!(v, Ok(Value::Float(3.4)));
        let v = Value::Complex(Complex::new(3.0, 4.0)).conj();
        assert_eq!(v, Ok(Value::Complex(Complex::new(3.0, -4.0))));
    }
    #[test]
    fn test_eq() {
        let v1 = Value::Float(3.0);
        let v2 = Value::Int(BigInt::from(3));
        let v = v1.eq(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::one())));
        let v1 = Value::Float(2.5);
        let v2 = Value::Ratio(BigRational::new(BigInt::from(5), BigInt::from(2)));
        let v = v1.eq(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::one())));
        let v1 = Value::Complex(Complex::new(3.0, 2.0));
        let v2 = Value::Complex(Complex::new(3.0, 2.0));
        let v = v1.eq(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::one())));
        let v1 = Value::Complex(Complex::new(3.0, 2.0));
        let v2 = Value::Float(3.0);
        let v = v1.eq(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::zero())));
    }
    #[test]
    fn test_neq() {
        let v1 = Value::Float(3.0);
        let v2 = Value::Int(BigInt::from(3));
        let v = v1.neq(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::zero())));
        let v1 = Value::Float(2.5);
        let v2 = Value::Ratio(BigRational::new(BigInt::from(5), BigInt::from(2)));
        let v = v1.neq(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::zero())));
        let v1 = Value::Complex(Complex::new(3.0, 2.0));
        let v2 = Value::Complex(Complex::new(3.0, 2.0));
        let v = v1.neq(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::zero())));
        let v1 = Value::Complex(Complex::new(3.0, 2.0));
        let v2 = Value::Float(3.0);
        let v = v1.neq(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::one())));
    }
    #[test]
    fn test_less() {
        let v1 = Value::Float(3.0);
        let v2 = Value::Int(BigInt::from(4));
        let v = v1.less(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::one())));
        let v1 = Value::Float(2.4);
        let v2 = Value::Ratio(BigRational::new(BigInt::from(5), BigInt::from(2)));
        let v = v1.less(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::one())));
        let v1 = Value::Complex(Complex::new(3.1, 2.1));
        let v2 = Value::Complex(Complex::new(3.0, 2.0));
        let v = v1.less(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::zero())));
        let v1 = Value::Complex(Complex::new(3.0, 2.0));
        let v2 = Value::Float(3.0);
        let v = v1.less(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::zero())));
    }
    #[test]
    fn test_greater() {
        let v1 = Value::Float(3.0);
        let v2 = Value::Int(BigInt::from(4));
        let v = v1.greater(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::zero())));
        let v1 = Value::Float(2.4);
        let v2 = Value::Ratio(BigRational::new(BigInt::from(5), BigInt::from(2)));
        let v = v1.greater(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::zero())));
        let v1 = Value::Complex(Complex::new(3.1, 2.1));
        let v2 = Value::Complex(Complex::new(3.0, 2.0));
        let v = v1.greater(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::one())));
        let v1 = Value::Complex(Complex::new(3.0, 2.0));
        let v2 = Value::Float(3.0);
        let v = v1.greater(v2);
        assert_eq!(v, Ok(Value::Int(BigInt::one())));
    }
    #[test]
    fn test_abs() {
        let v = Value::Float(3.0).abs();
        assert_eq!(v, Ok(Value::Float(3.0)));
        let v = Value::Float(-3.0).abs();
        assert_eq!(v, Ok(Value::Float(3.0)));
        let v = Value::Int(BigInt::from(3)).abs();
        assert_eq!(v, Ok(Value::Int(BigInt::from(3))));
        let v = Value::Int(BigInt::from(-3)).abs();
        assert_eq!(v, Ok(Value::Int(BigInt::from(3))));
        let v = Value::Ratio(BigRational::new(BigInt::from(3), BigInt::from(2))).abs();
        assert_eq!(v, Ok(Value::Ratio(BigRational::new(BigInt::from(3), BigInt::from(2)))));
        let v = Value::Ratio(BigRational::new(BigInt::from(-3), BigInt::from(2))).abs();
        assert_eq!(v, Ok(Value::Ratio(BigRational::new(BigInt::from(3), BigInt::from(2)))));
        let v = Value::Complex(Complex::new(3.0, -2.0)).abs();
        assert_eq!(v, Ok(Value::Complex(Complex::new(3.0, -2.0))));
        let v = Value::Complex(Complex::new(-3.0, -2.0)).abs();
        assert_eq!(v, Ok(Value::Complex(Complex::new(3.0, -2.0))));
    }
    #[test]
    fn test_sqr() {
        let v = Value::Complex(Complex::new(0.0, 3.0)).sqr();
        assert_eq!(v, Ok(Value::Float(-9.0)));
    }
    #[test]
    fn test_sqrt() {
        let v = Value::Int(BigInt::from(9)).sqrt();
        assert_eq!(v, Ok(Value::Int(BigInt::from(3))));
        let v = Value::Int(BigInt::from(2)).sqrt().unwrap();
        assert_eq!(v.clone().less(Value::Float(1.6)), Ok(Value::Int(BigInt::one())));
        assert_eq!(v.greater(Value::Float(1.3)), Ok(Value::Int(BigInt::one())));
        let v = Value::Float(0.5);
        let r = v.clone().sqr().unwrap().sqrt();
        assert_eq!(Ok(v), r);
        let v = Value::Float(-4.0);
        let r = v.sqrt();
        assert!(r.is_ok());
        let r = r.unwrap();
        assert_eq!(r, Value::Complex(Complex::new(0.0, 2.0)));
    }
    #[test]
    fn test_round() {
        let v = Value::Float(2.75);
        let a = v.clone().round();
        assert_eq!(a, Ok(Value::Int(BigInt::from(3))));
        let a = v.clone().ceil();
        assert_eq!(a, Ok(Value::Int(BigInt::from(3))));
        let a = v.clone().floor();
        assert_eq!(a, Ok(Value::Int(BigInt::from(2))));
        let v = Value::Ratio(BigRational::new(BigInt::from(9), BigInt::from(4)));
        let a = v.clone().round();
        assert_eq!(a, Ok(Value::Int(BigInt::from(2))));
        let a = v.clone().ceil();
        assert_eq!(a, Ok(Value::Int(BigInt::from(3))));
        let a = v.clone().floor();
        assert_eq!(a, Ok(Value::Int(BigInt::from(2))));
    }
    #[test]
    fn test_power() {
        let v = Value::Float(3.0);
        let pow = Value::Int(BigInt::from(3));
        let v = v.power(pow);
        assert_eq!(v, Ok(Value::Int(BigInt::from(27))));
        let v = Value::Ratio(BigRational::new(BigInt::from(2), BigInt::from(3)));
        let pow = Value::Int(BigInt::from(2));
        let v = v.power(pow);
        assert_eq!(v, Ok(Value::Ratio(BigRational::new(BigInt::from(4), BigInt::from(9)))));
        let v = Value::Float(3.0);
        let pow = Value::Float(2.0);
        let v = v.power(pow);
        assert_eq!(v, Ok(Value::Int(BigInt::from(9))));
    }
    #[test]
    fn test_factorial() {
        let v = Value::Float(3.0).fact();
        assert_eq!(v, Ok(Value::Int(BigInt::from(6))));
        let v = Value::Int(BigInt::from(5)).fact();
        assert_eq!(v, Ok(Value::Int(BigInt::from(120))));
    }
    #[test]
    fn test_bitwise() {
        let v = Value::Int(BigInt::from(4)).bit_or(Value::Int(BigInt::from(9)));
        assert_eq!(v, Ok(Value::Int(BigInt::from(13))));
        let v = Value::Int(BigInt::from(5)).bit_and(Value::Int(BigInt::from(14)));
        assert_eq!(v, Ok(Value::Int(BigInt::from(4))));
        let v = Value::Int(BigInt::from(5)).bit_xor(Value::Int(BigInt::from(14)));
        assert_eq!(v, Ok(Value::Int(BigInt::from(11))));
    }
    #[test]
    fn test_exp() {
        let v = Value::Float(0.5);
        let r = v.clone().exp().unwrap().ln();
        assert_eq!(Ok(v.clone()), r);
    }
    #[test]
    fn test_trigonometry() {
        let v = Value::Float(0.5);
        let r = v.clone().sin().unwrap().asin();
        assert_eq!(Ok(v.clone()), r);
        let r = v.clone().tan().unwrap().atan();
        assert_eq!(Ok(v), r);
    }
    #[test]
    fn test_img() {
        let v = Value::Complex(Complex::new(3.0, -4.0));
        let r = v.clone().im();
        assert_eq!(r, Ok(Value::Float(-4.0)));
        let r = v.clone().re();
        assert_eq!(r, Ok(Value::Float(3.0)));
        let r = v.clone().norm();
        assert_eq!(r, Ok(Value::Float(5.0)));
    }
}
