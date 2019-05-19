use std::f64::consts;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::errors::*;
use crate::value::*;

use lazy_static::lazy_static;

#[derive(Clone, Debug)]
pub(crate) enum Entry {
    Val(Value),
    Op(String, i32, bool),
    OpenB,
    Func(String, usize),
}

pub(crate) struct Stack {
    pub(crate) queue: Vec<Entry>,
    pub(crate) output: Vec<Entry>,
    values: Vec<Value>,
    pub result: Value,
    pub(crate) has_alt: bool,
    pub(crate) alt_result: String,
}

const PRI_IMMEDIATE: i32 = 99;
pub(crate) const FACTORIAL: &str = "!!!";
pub(crate) const UNARY_MINUS: &str = "---";

lazy_static! {
    pub(crate) static ref STD_FUNCS: Vec<&'static str> = [
        "sqr",
        "sqrt",
        "cbrt",
        "exp",
        "ln",
        "abs",
        "signum",
        "round",
        "ceil",
        "trunc",
        "floor",
        "ratio",
        "sin",
        "cos",
        "tan",
        "asin",
        "acos",
        "atan",
        "sinh",
        "cosh",
        "tanh",
        "asinh",
        "acosh",
        "atanh",
        "norm",
        "conj",
        "im",
        "re",
        "fract",
        "iif",
        "gcd",
        "lcm",
        "deg",
        "rad",
        "fib",
        "min",
        "max",
        "avg",
        "is_prime",
        "next_prime",
        "hex",
        "oct",
        "bin",
        "gamma",
        "solve",
        "zeroes",
        "roots",
    ]
    .to_vec();
}

macro_rules! one_arg_op {
    ($id:ident) => {
        fn $id(&mut self) -> CalcErrorResult {
            if self.values.is_empty() {
                return Err(CalcError::TooManyOps);
            }

            let v = self.values.pop().unwrap();
            let v = v.$id()?;
            self.values.push(v);
            Ok(())
        }
    }
}
macro_rules! two_arg_op {
    ($id:ident) => {
        fn $id(&mut self) -> CalcErrorResult {
            if self.values.len() < 2 {
                return Err(CalcError::TooManyOps);
            }

            let v2 = self.values.pop().unwrap();
            let v1 = self.values.pop().unwrap();
            let v = v1.$id(v2)?;
            self.values.push(v);
            Ok(())
        }
    }
}
macro_rules! function_op {
    ($id:ident) => {
        fn $id(&mut self, args: usize) -> CalcErrorResult {
            if args == 0 {
                return Err(CalcError::FunctionNoArgs(stringify!($id).to_string()));
            }
            if self.values.len() < args {
                return Err(CalcError::FunctionUnfinished(stringify!($id).to_string()));
            }

            // TODO: the func in the macro uses only one argument: the first
            let mut v = self.values.pop().unwrap();
            for _i in 0..args-1 {
                v = self.values.pop().unwrap();
            }
            let v = v.$id()?;
            self.values.push(v);
            Ok(())
        }
    }
}

impl Stack {
    fn priority(op: &str) -> (i32, bool) {
        match op {
            FACTORIAL => (PRI_IMMEDIATE, false),                 // immediate - factorial
            UNARY_MINUS | "~" | "!" => (20, true),               // negate, bit NOT
            "**" => (17, true),                                  // power
            "<<" | ">>" => (15, false),                          // bit shifts
            "*" | "/" | "//" | "%" => (12, false),               // mult, div, int div, mod
            "+" | "-" => (8, false),                             // add, sub
            "&" | "^" => (7, false),                             // bit AND/XOR
            "|" => (5, false),                                   // bit OR
            "&&" => (4, false),                                  // bit AND
            "||" => (3, false),                                  // bit AND
            "==" | "!=" | "<" | ">" | "<=" | ">=" => (2, false), // logical ops
            _ => (0, false),                                     // invalid op
        }
    }

    pub(crate) fn is_func(&self, s: &str) -> bool {
        for fname in STD_FUNCS.iter() {
            if *fname == s {
                return true;
            }
        }
        false
    }

    // move operators from the queue to output while the top operator in the
    // queue has equal or greater priority
    fn pop_while_priority(&mut self, priority: i32) {
        loop {
            if self.queue.is_empty() {
                return;
            }
            // queue is not empry, so unwrap is OK
            let e = self.queue.pop().unwrap();
            match &e {
                Entry::OpenB => {
                    self.queue.push(e);
                    return;
                }
                Entry::Func(..) => {
                    self.output.push(e);
                }
                Entry::Op(_, p, right) => {
                    if *p > priority || (*p == priority && !*right) {
                        self.output.push(e);
                    } else {
                        self.queue.push(e);
                        return;
                    }
                }
                _ => return, // unreachable
            }
        }
    }

    fn update_func_args(&mut self) {
        if self.queue.is_empty() {
            return;
        }

        if let Some(q) = self.queue.pop() {
            match &q {
                Entry::Func(name, args) => {
                    let args = args + 1;
                    self.queue.push(Entry::Func(name.to_string(), args));
                }
                _ => self.queue.push(q),
            }
        }
    }

    // move operators from the queue to output until the first bracket
    // or first argument separator
    fn pop_until_bracket(&mut self, keep_bracket: bool) -> CalcErrorResult {
        loop {
            if self.queue.is_empty() {
                return Err(CalcError::ClosingBracketMismatch);
            }

            // unwrap is ok - vector is not empty
            let e = self.queue.pop().unwrap();
            match &e {
                Entry::Val(..) | Entry::Op(..) | Entry::Func(..) => self.output.push(e),
                Entry::OpenB => {
                    self.update_func_args();
                    if keep_bracket {
                        self.queue.push(Entry::OpenB);
                    }
                    return Ok(());
                }
            }
        }
    }

    // move functions from the queue to output
    fn pop_functions(&mut self) -> CalcErrorResult {
        loop {
            if self.queue.is_empty() {
                return Ok(());
            }

            // unwrap is ok - vector is not empty
            let e = self.queue.pop().unwrap();
            match &e {
                Entry::Func(..) => self.output.push(e),
                _ => {
                    self.queue.push(e);
                    return Ok(());
                }
            }
        }
    }

    // move all operators from queue to output
    // Must be called only after the expression ends.
    // May return an error: e.g, UnclosedBracket
    fn pop_all(&mut self) -> CalcErrorResult {
        while let Some(v) = self.queue.pop() {
            match &v {
                Entry::OpenB => {} // do nothing - allows to omit last closing brackets
                Entry::Op(..) => self.output.push(v),
                Entry::Func(..) => self.output.push(v),
                _ => return Err(CalcError::Unreachable),
            }
        }
        Ok(())
    }

    // ------------ PUBLIC -----------------

    pub(crate) fn new() -> Self {
        Stack {
            queue: Vec::new(),
            output: Vec::new(),
            values: Vec::new(),
            result: Value::Float(0.0),
            has_alt: false,
            alt_result: "".to_owned(),
        }
    }

    pub(crate) fn push(&mut self, op: &str, val: Option<Value>) -> CalcErrorResult {
        if op.is_empty() {
            if let Some(v) = val {
                self.output.push(Entry::Val(v))
            } else {
                return Err(CalcError::EmptyValue);
            }
            return Ok(());
        }

        if self.is_func(op) {
            self.queue.push(Entry::Func(op.to_owned(), 0));
            return Ok(());
        }

        if op == "(" {
            self.queue.push(Entry::OpenB);
            return Ok(());
        }

        if op == ")" {
            return self.pop_until_bracket(false);
        }
        if op == ";" {
            return self.pop_until_bracket(true);
        }

        let (pri, right_assoc) = Stack::priority(op);
        if pri == 0 {
            return Err(CalcError::InvalidOp(op.to_owned()));
        }

        if pri == PRI_IMMEDIATE {
            self.pop_functions()?;
            self.output.push(Entry::Op(op.to_owned(), pri, false));
            return Ok(());
        }

        self.pop_while_priority(pri);
        self.queue.push(Entry::Op(op.to_owned(), pri, right_assoc));

        Ok(())
    }

    pub(crate) fn increase_func_argc(&mut self) -> CalcErrorResult {
        if let Some(e) = self.queue.pop() {
            match &e {
                Entry::Func(fname, argc) => {
                    self.queue.push(Entry::Func(fname.to_string(), argc + 1));
                }
                _ => self.queue.push(e),
            }
        }
        Ok(())
    }

    pub(crate) fn calculate(&mut self) -> CalcResult {
        self.pop_all()?;
        if self.output.is_empty() {
            return Err(CalcError::EmptyExpression);
        }

        self.result = Value::Float(0.0);
        self.values = Vec::new();

        for i in 0..self.output.len() {
            self.has_alt = false;
            let o = self.output[i].clone();
            match o {
                Entry::Val(v) => {
                    self.values.push(v.clone());
                }
                Entry::Op(op, ..) => {
                    self.process_operator(&op)?;
                }
                Entry::Func(fname, args) => {
                    self.process_function(&fname, args)?;
                }
                _ => return Err(CalcError::Unreachable),
            }
        }

        if self.values.len() != 1 {
            return Err(CalcError::InsufficientOps);
        }

        // values is never empty after calculation - unwrap is fine
        self.result = self.values.pop().unwrap();
        Ok(self.result.clone())
    }

    fn process_operator(&mut self, op: &str) -> CalcErrorResult {
        match op {
            "/" => self.divide(),
            "*" => self.multiply(),
            "+" => self.addition(),
            "-" => self.subtract(),
            "//" => self.div_int(),
            "%" => self.reminder(),
            "**" => self.power(),
            UNARY_MINUS => self.negate(),
            FACTORIAL => self.fact(),
            "<<" => self.bit_shl(),
            ">>" => self.bit_shr(),
            "~" => self.bit_not(),
            "!" => self.logical_not(),
            "==" => self.eq(),
            "!=" => self.neq(),
            ">" => self.greater(),
            ">=" => self.greatereq(),
            "<" => self.less(),
            "<=" => self.lesseq(),
            "^" => self.bit_xor(),
            "&" => self.bit_and(),
            "|" => self.bit_or(),
            "&&" => self.logical_and(),
            "||" => self.logical_or(),
            _ => Err(CalcError::InvalidOp(op.to_string())),
        }
    }

    fn process_function(&mut self, fname: &str, args: usize) -> CalcErrorResult {
        match fname {
            "sin" => self.sin(args),
            "cos" => self.cos(args),
            "tan" => self.tan(args),
            "asin" => self.asin(args),
            "acos" => self.acos(args),
            "atan" => self.atan(args),
            "sinh" => self.sinh(args),
            "cosh" => self.cosh(args),
            "tanh" => self.tanh(args),
            "asinh" => self.asinh(args),
            "acosh" => self.acosh(args),
            "atanh" => self.atanh(args),
            "ln" => self.ln(args),
            "exp" => self.exp(args),
            "norm" => self.norm(args),
            "re" => self.re(args),
            "im" => self.im(args),
            "conj" => self.conj(args),
            "round" => self.round(args),
            "ceil" => self.ceil(args),
            "floor" => self.floor(args),
            "trunc" => self.trunc(args),
            "abs" => self.abs(args),
            "signum" => self.signum(args),
            "sqr" => self.sqr(args),
            "sqrt" => self.sqrt(args),
            "cbrt" => self.cbrt(args),
            "ratio" => self.ratio(args),
            "fract" => self.fract(args),
            "iif" => self.iif(args),
            "gcd" => self.gcd(args),
            "lcm" => self.lcm(args),
            "deg" => self.deg(args),
            "rad" => self.rad(args),
            "fib" => self.fib(args),
            "min" => self.min(args),
            "max" => self.max(args),
            "avg" => self.avg(args),
            "is_prime" => self.prime(args),
            "next_prime" => self.next_prime(args),
            "hex" => self.hex(args),
            "oct" => self.oct(args),
            "bin" => self.bin(args),
            "gamma" => self.gamma(args),
            "solve" | "zeroes" | "roots" => self.solve(args),
            _ => Err(CalcError::InvalidOp(fname.to_string())),
        }
    }

    one_arg_op!(negate);
    one_arg_op!(logical_not);
    one_arg_op!(fact);
    one_arg_op!(bit_not);

    two_arg_op!(eq);
    two_arg_op!(neq);
    two_arg_op!(less);
    two_arg_op!(lesseq);
    two_arg_op!(greater);
    two_arg_op!(greatereq);
    two_arg_op!(logical_and);
    two_arg_op!(logical_or);
    two_arg_op!(bit_or);
    two_arg_op!(bit_xor);
    two_arg_op!(bit_and);
    two_arg_op!(bit_shl);
    two_arg_op!(bit_shr);
    two_arg_op!(power);
    two_arg_op!(divide);
    two_arg_op!(reminder);
    two_arg_op!(div_int);
    two_arg_op!(addition);
    two_arg_op!(subtract);
    two_arg_op!(multiply);

    function_op!(sin);
    function_op!(cos);
    function_op!(tan);
    function_op!(asin);
    function_op!(acos);
    function_op!(atan);
    function_op!(sinh);
    function_op!(cosh);
    function_op!(tanh);
    function_op!(asinh);
    function_op!(acosh);
    function_op!(atanh);

    function_op!(norm);
    function_op!(conj);
    function_op!(im);
    function_op!(re);

    function_op!(fract);
    function_op!(abs);
    function_op!(floor);
    function_op!(ceil);
    function_op!(round);
    function_op!(trunc);
    function_op!(sqr);
    function_op!(sqrt);
    function_op!(cbrt);
    function_op!(exp);
    function_op!(ln);
    function_op!(signum);

    fn iif(&mut self, args: usize) -> CalcErrorResult {
        if args < 3 || self.values.len() < 3 {
            return Err(CalcError::FunctionNotEnoughArgs("iif".to_string(), 3));
        }

        // remove redundant arguments
        for _i in 0..args - 3 {
            let _ = self.values.pop().unwrap();
        }
        let v_false = self.values.pop().unwrap();
        let v_true = self.values.pop().unwrap();
        let v_cond = self.values.pop().unwrap();
        if v_cond.is_zero() {
            self.values.push(v_false);
        } else {
            self.values.push(v_true);
        }
        Ok(())
    }

    fn gcd(&mut self, args: usize) -> CalcErrorResult {
        if args < 2 || self.values.len() < 2 {
            return Err(CalcError::FunctionNotEnoughArgs("gcd".to_string(), 2));
        }
        let mut v = self.values.pop().unwrap();
        for _i in 0..args - 1 {
            let tmp = self.values.pop().unwrap();
            v = v.gcd(tmp)?;
        }
        self.values.push(v);
        Ok(())
    }

    fn lcm(&mut self, args: usize) -> CalcErrorResult {
        if args < 2 || self.values.len() < 2 {
            return Err(CalcError::FunctionNotEnoughArgs("lcm".to_string(), 2));
        }
        let mut v = self.values.pop().unwrap();
        for _i in 0..args - 1 {
            let tmp = self.values.pop().unwrap();
            v = v.lcm(tmp)?;
        }
        self.values.push(v);
        Ok(())
    }

    fn deg(&mut self, args: usize) -> CalcErrorResult {
        if args == 0 || self.values.is_empty() {
            return Err(CalcError::FunctionNoArgs("deg".to_string()));
        }
        for _i in 0..args - 1 {
            let _ = self.values.pop().unwrap();
        }
        let v = self.values.pop().unwrap();
        let rad = v.into_raw_f64()?;
        let deg = rad * 180.0 / consts::PI;
        self.values.push(Value::Float(deg));
        Ok(())
    }

    fn rad(&mut self, args: usize) -> CalcErrorResult {
        if args == 0 || self.values.is_empty() {
            return Err(CalcError::FunctionNoArgs("rad".to_string()));
        }
        for _i in 0..args - 1 {
            let _ = self.values.pop().unwrap();
        }
        let v = self.values.pop().unwrap();
        let deg = v.into_raw_f64()?;
        let rad = deg * consts::PI / 180.0;
        self.values.push(Value::Float(rad));
        Ok(())
    }

    fn fib(&mut self, args: usize) -> CalcErrorResult {
        if args == 0 || self.values.is_empty() {
            return Err(CalcError::FunctionNoArgs("fib".to_string()));
        }
        for _i in 0..args - 1 {
            let _ = self.values.pop().unwrap();
        }
        let v = self.values.pop().unwrap();
        match v {
            Value::Int(i) => {
                if i < BigInt::zero() {
                    return Err(CalcError::NotForNegativeInt("fib".to_string()));
                }
                // TODO: select better N
                if i > BigInt::from(100_000) {
                    let s = format!("{}", i);
                    return Err(CalcError::ArgumentOutOfRange(
                        "fib".to_string(),
                        s,
                        "[0..1_00_000]".to_string(),
                    ));
                }
                if i.is_zero() {
                    self.values.push(Value::Int(BigInt::zero()));
                    return Ok(());
                }
                let mut fb = BigInt::one();
                let mut prev = BigInt::zero();
                let mut i = i;
                while i > BigInt::one() {
                    let tmp = fb.clone() + prev;
                    prev = fb;
                    fb = tmp;
                    i -= BigInt::one();
                }
                self.values.push(Value::Int(fb));
                Ok(())
            }
            _ => Err(CalcError::OnlyInt("fib".to_string())),
        }
    }

    fn ratio(&mut self, args: usize) -> CalcErrorResult {
        if args == 0 {
            return Err(CalcError::FunctionNoArgs("ratio".to_string()));
        }
        if self.values.len() < args {
            return Err(CalcError::FunctionUnfinished("ratio".to_string()));
        }

        if args == 2 {
            let v2 = self.values.pop().unwrap();
            let v1 = self.values.pop().unwrap();
            let v1 = v1.into_raw_big_int()?;
            let v2 = v2.into_raw_big_int()?;
            self.values.push(Value::Ratio(BigRational::new(v1, v2)));
            return Ok(());
        }

        let mut v = self.values.pop().unwrap();
        for _i in 0..args - 1 {
            v = self.values.pop().unwrap();
        }
        let v = v.ratio()?;
        self.values.push(v);
        Ok(())
    }

    fn min_max<F>(&mut self, args: usize, fname: &'static str, f: F) -> CalcErrorResult
    where
        F: Fn(Value, Value) -> Value,
    {
        if args == 0 || self.values.is_empty() {
            return Err(CalcError::FunctionNoArgs(fname.to_string()));
        }

        let mut v = self.values.pop().unwrap();
        for _i in 1..args {
            let cmp = self.values.pop().unwrap();
            v = f(v, cmp);
        }
        self.values.push(v);
        Ok(())
    }

    fn min(&mut self, args: usize) -> CalcErrorResult {
        self.min_max(args, "min", |v1, v2| {
            let r = if let Ok(v) = v1.clone().less(v2.clone()) {
                v
            } else {
                Value::Int(BigInt::zero())
            };
            if r.is_zero() {
                v2
            } else {
                v1
            }
        })
    }

    fn max(&mut self, args: usize) -> CalcErrorResult {
        self.min_max(args, "max", |v1, v2| {
            let r = if let Ok(v) = v1.clone().greater(v2.clone()) {
                v
            } else {
                Value::Int(BigInt::zero())
            };
            if r.is_zero() {
                v2
            } else {
                v1
            }
        })
    }

    fn avg(&mut self, args: usize) -> CalcErrorResult {
        if args < 2 || self.values.len() < 2 {
            return Ok(());
        }

        let mut v = self.values.pop().unwrap();
        for _i in 1..args {
            let a = self.values.pop().unwrap();
            v = v.addition(a)?;
        }
        let av = Value::Int(BigInt::from(args));
        v = v.divide(av)?;
        self.values.push(v);
        Ok(())
    }

    fn prime(&mut self, args: usize) -> CalcErrorResult {
        if args == 0 || self.values.is_empty() {
            return Err(CalcError::FunctionNoArgs("is_prime".to_string()));
        }
        for _i in 0..args - 1 {
            let _ = self.values.pop().unwrap();
        }

        let v = self.values.pop().unwrap();
        let res = v.prime()?;
        self.values.push(res);
        Ok(())
    }

    fn next_prime(&mut self, args: usize) -> CalcErrorResult {
        if args == 0 || self.values.is_empty() {
            return Err(CalcError::FunctionNoArgs("is_prime".to_string()));
        }
        for _i in 0..args - 1 {
            let _ = self.values.pop().unwrap();
        }

        let v = self.values.pop().unwrap();
        let v = v.into_raw_big_int()?;
        let mut v = v + BigInt::one();
        if v.clone() % BigInt::from(2) == BigInt::zero() {
            v += BigInt::one();
        }
        loop {
            let res = Value::Int(v.clone()).prime()?;
            if !res.is_zero() {
                break;
            }
            v += BigInt::from(2);
        }
        self.values.push(Value::Int(v));
        Ok(())
    }

    fn int_to_base(&mut self, args: usize, base: u32, prefix: &str) -> CalcErrorResult {
        if base < 2 || base > 36 {
            return Err(CalcError::InvalidAgrument("to_base".to_string(), "base".to_string()));
        }
        if args == 0 || self.values.is_empty() {
            return Err(CalcError::FunctionNoArgs("hex".to_string()));
        }
        for _i in 0..args - 1 {
            let _ = self.values.pop().unwrap();
        }

        let v = self.values.pop().unwrap();

        let vi = v.clone().into_raw_big_int()?;
        self.has_alt = true;
        self.alt_result = format!("{}{}", prefix, vi.to_str_radix(base));

        self.values.push(v);
        Ok(())
    }

    fn hex(&mut self, args: usize) -> CalcErrorResult {
        self.int_to_base(args, 16u32, "0x")
    }

    fn oct(&mut self, args: usize) -> CalcErrorResult {
        self.int_to_base(args, 8u32, "0o")
    }

    fn bin(&mut self, args: usize) -> CalcErrorResult {
        self.int_to_base(args, 2u32, "0b")
    }

    fn gamma(&mut self, args: usize) -> CalcErrorResult {
        if args == 0 || self.values.is_empty() {
            return Err(CalcError::FunctionNoArgs("gamma".to_string()));
        }
        for _i in 0..args - 1 {
            let _ = self.values.pop().unwrap();
        }

        let v = self.values.pop().unwrap();
        if v.is_zero() {
            return Err(CalcError::InvalidAgrument("gamma".to_string(), "0".to_string()));
        }

        // arbitrary number of steps. It seems a number between 18-30 gives the
        // best accuracy for f64
        const STEPS: usize = 19;

        // https://en.wikipedia.org/wiki/Spouge%27s_approximation
        let mut sum = Value::Float((2.0f64 * consts::PI).sqrt());
        let mut d = Value::Float(1.0f64);
        let mut do_neg = false;
        for k in 1..STEPS {
            let a = Value::Int(BigInt::from(STEPS - k));
            let a = a.power(Value::Float(k as f64 - 0.5f64))?;
            let e = Value::Float((STEPS - k) as f64).exp()?;
            let e = e.divide(d.clone())?;
            let a = a.multiply(e)?;
            let adder = Value::Float(k as f64).addition(v.clone())?;
            let a = a.divide(adder)?;
            if do_neg {
                sum = sum.clone().subtract(a)?;
            } else {
                sum = sum.clone().addition(a)?;
            }
            d = d.multiply(Value::Float(k as f64))?;
            do_neg = !do_neg;
        }
        let m1 = Value::Float(STEPS as f64).addition(v.clone())?;
        let pwr = v.clone().addition(Value::Float(0.5f64))?;
        let m1 = m1.power(pwr)?;
        let m2 = Value::Float(-(STEPS as f64)).subtract(v.clone())?;
        let m2 = m2.exp()?;

        let res = m1.multiply(m2)?;
        let res = res.multiply(sum)?;

        self.values.push(res);
        Ok(())
    }

    fn solve(&mut self, args: usize) -> CalcErrorResult {
        if args < 2 || self.values.is_empty() {
            return Err(CalcError::FunctionNotEnoughArgs("solve".to_string(), 2));
        }

        // linear
        if args == 2 {
            let c = self.values.pop().unwrap();
            let x = self.values.pop().unwrap();
            if x.is_zero() {
                if !c.is_zero() {
                    return Err(CalcError::NoRoots);
                }

                self.values.push(Value::Int(BigInt::from(0)));
                return Ok(());
            }

            self.has_alt = true;
            let cstr = if c.is_positive() {
                format!("+{}", c)
            } else {
                format!("{}", c)
            };
            let r = c.divide(x.clone())?;
            self.has_alt = true;
            self.alt_result = format!("{}*x{}=0, x={}", x, cstr, r);
            self.values.push(r);

            return Ok(());
        }

        // square
        for _i in 0..args - 3 {
            let _ = self.values.pop().unwrap();
        }
        let c = self.values.pop().unwrap();
        let b = self.values.pop().unwrap();
        let a = self.values.pop().unwrap();
        if a.is_zero() {
            return Err(CalcError::NoRoots);
        }

        let d1 = b.clone().sqr()?;
        let d2 = Value::Int(BigInt::from(4)).multiply(a.clone())?;
        let d2 = d2.multiply(c.clone())?;
        let d = d1.subtract(d2)?;
        let d = d.sqrt()?;
        let q = if b.is_positive() {
            let t = b.clone().negate()?;
            t.subtract(d.clone())?
        } else {
            let t = b.clone().negate()?;
            t.addition(d.clone())?
        };
        let q = q.divide(Value::Int(BigInt::from(2)))?;
        let x1 = q.clone().divide(a.clone())?;
        let x2 = c.clone().divide(q)?;
        let bstr = if b.is_positive() {
            format!("+{}", b)
        } else {
            format!("{}", b)
        };
        let cstr = if c.is_positive() {
            format!("+{}", c)
        } else {
            format!("{}", c)
        };
        if d.is_zero() {
            self.has_alt = true;
            self.alt_result = format!("{}*x**2{}*x{}=0, x={}", a, bstr, cstr, x1);
        } else {
            self.has_alt = true;
            self.alt_result = format!("{}*x**2{}*x{}=0, x1={}, x2={}", a, bstr, cstr, x1, x2);
        }
        self.values.push(x1);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    #[test]
    fn test_simple_order() {
        let mut stack = Stack::new();
        // 2 + 3 * 2 + 5 = 13
        let _ = stack.push("", Some(Value::Int(BigInt::from(2))));
        let _ = stack.push("+", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(3))));
        let _ = stack.push("*", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(2))));
        let _ = stack.push("+", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(5))));
        let v = stack.calculate();
        assert_eq!(v, Ok(Value::Int(BigInt::from(13))));
    }
    #[test]
    fn test_braces() {
        let mut stack = Stack::new();
        // 2 + 3 * (2 + 5) + 1 = 13
        let _ = stack.push("", Some(Value::Int(BigInt::from(2))));
        let _ = stack.push("+", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(3))));
        let _ = stack.push("*", None);
        let _ = stack.push("(", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(2))));
        let _ = stack.push("+", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(5))));
        let _ = stack.push(")", None);
        let _ = stack.push("+", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(1))));
        let v = stack.calculate();
        assert_eq!(v, Ok(Value::Int(BigInt::from(24))));
    }
    #[test]
    fn test_functions() {
        let mut stack = Stack::new();
        // 2 + sqr(5) - sqr(4; 2) = 11
        let _ = stack.push("", Some(Value::Int(BigInt::from(2))));
        let _ = stack.push("+", None);
        let _ = stack.push("sqr", None);
        let _ = stack.push("(", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(5))));
        let _ = stack.push(")", None);
        let _ = stack.push("-", None);
        let _ = stack.push("sqr", None);
        let _ = stack.push("(", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(4))));
        let _ = stack.push(";", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(2))));
        let _ = stack.push(")", None);
        let v = stack.calculate();
        assert_eq!(v, Ok(Value::Int(BigInt::from(11))));
    }
    #[test]
    fn test_power() {
        let mut stack = Stack::new();
        // 5 + 2 ** 2 ** 3 + 1 = 262
        let _ = stack.push("", Some(Value::Int(BigInt::from(5))));
        let _ = stack.push("+", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(2))));
        let _ = stack.push("**", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(2))));
        let _ = stack.push("**", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(3))));
        let _ = stack.push("+", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(1))));
        let v = stack.calculate();
        assert_eq!(v, Ok(Value::Int(BigInt::from(262))));
    }
    #[test]
    fn test_factorial() {
        let mut stack = Stack::new();
        // 5 + 2 ** 2 ** 3 + 1 = 262
        let _ = stack.push("", Some(Value::Int(BigInt::from(3))));
        let _ = stack.push(FACTORIAL, None);
        let _ = stack.push("+", None);
        let _ = stack.push("(", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(3))));
        let _ = stack.push("+", None);
        let _ = stack.push("", Some(Value::Int(BigInt::from(2))));
        let _ = stack.push(")", None);
        let _ = stack.push(FACTORIAL, None);
        let v = stack.calculate();
        assert_eq!(v, Ok(Value::Int(BigInt::from(126))));
    }
}
