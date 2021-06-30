use pest::Parser;
use std::f64::consts::{E, PI};

use crate::errors::*;
use crate::stack::{Stack, FACTORIAL, PERCENT_ADD, PERCENT_DIV, PERCENT_MUL, PERCENT_SUB, STD_FUNCS, UNARY_MINUS};
use crate::value::*;

#[derive(Parser)]
#[grammar = "calc.pest"]
pub struct CalcParser;

pub const PHI: f64 = 1.618_033_988_749_895;
const LAST_RESULT: &str = "ans";

/// holds user user-defined variable
pub struct Variable {
    name: String,
    value: Value,
}
impl Variable {
    pub fn new(name: &str, value: Value) -> Self {
        Variable {
            name: name.to_string(),
            value,
        }
    }
}

/// holds the current state of the engine, e.g list of all previously used variables
pub struct CalcState {
    variables: Vec<Variable>,
    is_last_value: bool,
    is_last_func: bool,
    pub has_alt: bool,
    pub alt_result: String,
}

impl Default for CalcState {
    fn default() -> CalcState {
        CalcState {
            variables: Vec::new(),
            is_last_value: false,
            is_last_func: false,
            has_alt: true,
            alt_result: "".to_owned(),
        }
    }
}

impl CalcState {
    pub fn new() -> Self {
        Default::default()
    }

    /// Returns a constant value by its name. Name is caseinsensitive
    pub fn constant(&self, name: &str) -> Option<Value> {
        let a = name.to_lowercase();
        match a.as_str() {
            "e" => Some(Value::Float(E)),
            "pi" => Some(Value::Float(PI)),
            "phi" | "golden" | "gold" => Some(Value::Float(PHI)),
            _ => None,
        }
    }

    /// Returns a variable value by its name. Name is caseinsensitive
    pub fn variable(&self, name: &str) -> Option<Value> {
        let low = name.to_lowercase();
        for v in &self.variables {
            if v.name == low {
                return Some(v.value.clone());
            }
        }
        None
    }

    /// Creates a new variable or replace existing one with a new value.
    /// The function does not check variable's name for validity. In case
    /// of its name conflicts with existing function name, the variable
    /// will be inaccessible from expression evaluator
    pub fn add_variable(&mut self, name: &str, val: Value) {
        let name = name.to_lowercase();
        for v in &mut self.variables {
            if v.name == name {
                v.value = val;
                return;
            }
        }
        self.variables.push(Variable::new(&name, val));
    }

    /// Returns the result of the last successful evaluation
    pub fn result(&self) -> Option<Value> {
        self.variable(LAST_RESULT)
    }

    /// Check if variable name is valid:
    /// - name convention
    /// - does not conflict with any constant
    /// - does not conflist with any function
    /// - does not conflict with special variables, like `ans`
    pub fn variable_name_validate(&self, name: &str) -> Result<(), &'static str> {
        let name = name.to_lowercase();
        if let Some(p) = name.find(|c: char| ('a'..='z').contains(&c)) {
            if p != 0 {
                return Err("Variable name must start with 'a'..'z'");
            }
        } else {
            return Err("Variable name must start with 'a'..'z'");
        }

        let p = name.find(|c: char| c != '_' && !('0'..='9').contains(&c) && !('a'..='z').contains(&c));
        if p.is_some() {
            return Err("Variable name must contain only Latin letters, digits, and underscore");
        }

        if self.constant(&name).is_some() {
            return Err("Cannot assign a new value to a constant");
        }
        if name == LAST_RESULT {
            return Err("The name is reserved for an internal variable");
        }

        for fname in STD_FUNCS.iter() {
            if fname == &name {
                return Err("Function name cannot be used as a variable");
            }
        }

        Ok(())
    }
}

macro_rules! process_value {
    ($id: ident, $stack: ident, $state: ident, $val: ident) => {
        if $state.is_last_func {
            $stack.push("(", None)?;
        } else if $state.is_last_value {
            $stack.push("*", None)?;
        }
        let v = Value::$id(&$val)?;
        $stack.push("", Some(v))?;
        if $state.is_last_func {
            $stack.push(")", None)?;
        }
        $state.is_last_value = true;
        $state.is_last_func = false;
    };
}

struct PrepRule {
    r: Rule,
    v: String,
}

fn fixup_last_prc_op(pairs: &mut Vec<PrepRule>) -> bool {
    let mut id: usize = pairs.len() - 1;
    let mut level = 0;
    while id > 0 {
        let r = pairs[id].r;
        let v = pairs[id].v.clone();
        match r {
            Rule::close_b => level += 1,
            Rule::open_b => level -= 1,
            Rule::operator if level == 0 => match v.as_str() {
                "+" => {
                    pairs[id].v = PERCENT_ADD.to_string();
                    return true;
                }
                "-" => {
                    pairs[id].v = PERCENT_SUB.to_string();
                    return true;
                }
                "*" => {
                    pairs[id].v = PERCENT_MUL.to_string();
                    return true;
                }
                "/" => {
                    pairs[id].v = PERCENT_DIV.to_string();
                    return true;
                }
                _ => return false,
            },
            _ => {}
        }
        id -= 1;
    }
    false
}

fn preprocess_expr(expr: &str) -> Result<Vec<PrepRule>, CalcError> {
    let pairs = match CalcParser::parse(Rule::expr, expr) {
        Ok(p) => p,
        // detailed error from pest parser
        // Err(e) => return Err(CalcError::ParseFailed(e.to_string())),
        // rcalc own error
        Err(..) => return Err(CalcError::ParseFailed("invalid expression".to_string())),
    };
    let mut is_last_prc = false;
    let mut preps: Vec<PrepRule> = Vec::new();
    for pair in pairs {
        let rule = pair.as_rule();
        let val = pair.as_span().as_str().to_lowercase();
        match rule {
            Rule::close_b | Rule::arg_sep | Rule::operator => {
                let is_prc = val == "%";
                if is_last_prc {
                    let _ = preps.pop();
                    if !fixup_last_prc_op(&mut preps) {
                        preps.push(PrepRule {
                            r: Rule::operator,
                            v: "%".to_string(),
                        });
                    }
                }
                preps.push(PrepRule { r: rule, v: val });
                is_last_prc = is_prc;
            }
            _ => {
                is_last_prc = val == "%";
                preps.push(PrepRule { r: rule, v: val });
            }
        }
    }
    if is_last_prc {
        let _ = preps.pop();
        if !fixup_last_prc_op(&mut preps) {
            preps.push(PrepRule {
                r: Rule::operator,
                v: "%".to_string(),
            });
        };
    }
    Ok(preps)
}

/// evaluates a given expression and returns either result or error
pub fn eval(expr: &str, state: &mut CalcState) -> CalcResult {
    state.is_last_value = false;
    state.is_last_func = false;
    state.has_alt = false;

    let rules = preprocess_expr(expr)?;
    let mut stk = Stack::new();
    for pair in rules {
        let rule = pair.r;
        let val = pair.v;
        match rule {
            Rule::int | Rule::fulluint | Rule::hex | Rule::bin | Rule::oct => {
                process_value!(from_str_integer, stk, state, val);
            }
            Rule::float => {
                process_value!(from_str_float, stk, state, val);
            }
            Rule::ratio => {
                process_value!(from_str_ratio, stk, state, val);
            }
            Rule::degreefloat | Rule::fulldegree => {
                process_value!(from_str_angle, stk, state, val);
            }
            Rule::complex => {
                // distinguish between "1 - 2+i4" and "1 - -2+i4"
                #[allow(clippy::branches_sharing_code)]
                if state.is_last_value && val.starts_with('-') {
                    stk.push("-", None)?;
                    let slice = val[1..].to_string();
                    state.is_last_value = false;
                    state.is_last_func = false;
                    process_value!(from_str_complex, stk, state, slice);
                } else {
                    process_value!(from_str_complex, stk, state, val);
                }
            }
            Rule::open_b => {
                if state.is_last_value {
                    stk.push("*", None)?;
                }
                stk.push("(", None)?;
                state.is_last_value = false;
                state.is_last_func = false;
            }
            Rule::close_b => {
                stk.push(")", None)?;
                state.is_last_value = true;
                state.is_last_func = false;
            }
            Rule::arg_sep => {
                stk.push(";", None)?;
                state.is_last_value = false;
                state.is_last_func = false;
            }
            Rule::operator => {
                if val == "+" && !state.is_last_value {
                    state.is_last_value = false;
                } else if val == "-" && (!state.is_last_value || state.is_last_func) {
                    if state.is_last_func {
                        stk.push("(", None)?;
                        stk.push(")", None)?;
                        stk.push("-", None)?;
                    } else {
                        stk.push(UNARY_MINUS, None)?;
                    }
                    state.is_last_value = false;
                } else if val == "!" && state.is_last_value {
                    stk.push(FACTORIAL, None)?;
                    state.is_last_value = true;
                } else {
                    stk.push(&val, None)?;
                    state.is_last_value = false;
                }
                state.is_last_func = false;
            }
            Rule::ident => {
                if stk.is_func(&val) {
                    if state.is_last_value {
                        stk.push("*", None)?;
                    } else if state.is_last_func {
                        stk.increase_func_argc()?;
                    }
                    stk.push(&val, None)?;
                    state.is_last_value = false;
                    state.is_last_func = true;
                } else {
                    if let Some(v) = state.constant(&val) {
                        stk.push("", Some(v))?;
                    } else if let Some(v) = state.variable(&val) {
                        stk.push("", Some(v))?;
                    } else {
                        return Err(CalcError::VarUndeclared(val.to_string()));
                    }
                    state.is_last_value = true;
                    state.is_last_func = false;
                }
            }
            _ => return Err(CalcError::Unreachable),
        }
    }
    let output = stk.calculate();
    if let Ok(ref v) = output {
        state.add_variable(LAST_RESULT, v.clone());
        if stk.has_alt {
            state.has_alt = true;
            state.alt_result = stk.alt_result;
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_complex::Complex;
    use num_rational::BigRational;

    #[test]
    fn test_expr() {
        let mut state: CalcState = CalcState::new();
        let v = eval("2+3", &mut state);
        assert_eq!(v, Ok(Value::Int(BigInt::from(5))));
        let v = eval("(3+2)(4-9)", &mut state);
        assert_eq!(v, Ok(Value::Int(BigInt::from(-25))));
        let v = eval("sin(1;2;3)", &mut state);
        assert_eq!(v, Ok(Value::Float(1.0f64.sin())));
        let v = eval("(3+9)sin(1)", &mut state);
        assert_eq!(v, Ok(Value::Float(12.0f64 * 1.0f64.sin())));
        let v = eval("1\\2+3\\5", &mut state);
        assert_eq!(
            v,
            Ok(Value::Ratio(BigRational::new(BigInt::from(11), BigInt::from(10))))
        );
        let v = eval("1+2+i3", &mut state);
        assert_eq!(v, Ok(Value::Complex(Complex::new(3.0, 3.0))));
        let v = eval("1-2+i3", &mut state);
        assert_eq!(v, Ok(Value::Complex(Complex::new(-1.0, -3.0))));
        let v = eval("1--2+i3", &mut state);
        assert_eq!(v, Ok(Value::Complex(Complex::new(3.0, -3.0))));
        let v = eval("10+--5!/10", &mut state);
        assert_eq!(v, Ok(Value::Int(BigInt::from(22))));
        let v = eval("10+-!!20*3", &mut state);
        assert_eq!(v, Ok(Value::Int(BigInt::from(7))));
        let v = eval("1 + sin cos 2 * 10", &mut state);
        assert_eq!(v, Ok(Value::Float(2.0f64.cos().sin() * 10.0 + 1.0)));
    }

    #[test]
    fn test_corner_cases() {
        let mut state: CalcState = CalcState::new();
        let exprs: [&'static str; 18] = [
            // auto: float -> complex
            "ln(-3) * sqrt(-5) + asin(5)",
            // exp is float, so the result is inaccurate f64
            "exp(100) * 12345678901234567890 * 987654321012345678901234567890",
            // exp is converted to big int, so the result is exact
            "round(exp(100)) * 12345678901234567890 * 987654321012345678901234567890",
            // a lot of single argument functions without brackets
            "sin cos sin cos sin cos 0.1",
            // should generate the same result as above
            "sin (cos( sin( cos (sin (cos (0.1))))))",
            // a lot of unary pluses
            "2+++++3sqrt 5",
            // double factorial should have higher priority than multiplication
            "3!!*2",
            // negated complex with positive real part
            "1.0+9.2i-2.3-4.8i",
            // negated complex with negative real part
            "1.0+9.2i--2.3-4.8i",
            // raise to negative floating point degree
            "2**-e",
            // different cases to test automatic insertion of brackets and multiplication sign
            "sin cos 2 30",
            "sin cos (2*30)",
            "sin (cos (2))*30",
            "sin (cos 2)*30",
            "sin cos 2*30",
            "sin(1)sin(1)",
            "sin 1 sin 1",
            "sin 1 sin(1)",
        ];
        let ress: [&'static str; 18] = [
            "-5.45401840424583+0.16414008881733767i",
            "3.2776919587749234e92",
            "327769195877492364977545717691598341790414097481269687584256420446284592691174142251735449600",
            "0.7270679494248203",
            "0.7270679494248203",
            "8.70820393249937",
            "1440",
            "-1.2999999999999999+14.0i",
            "3.3+14.0i",
            "0.15195522325791298",
            "-12.127174615567974",
            "-0.8148167252856553",
            "-12.127174615567974",
            "-12.127174615567974",
            "-12.127174615567974",
            "0.7080734182735712",
            "0.7080734182735712",
            "0.7080734182735712",
        ];

        for (i, expr) in exprs.to_vec().iter().enumerate() {
            let res = eval(expr, &mut state);
            let res_str = match res {
                Ok(v) => format!("{}", v),
                Err(e) => format!("{:?}", e),
            };
            assert_eq!(res_str, ress[i].to_string());
        }
    }
}
