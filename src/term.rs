use crate::env::Env;
use crate::Symbol;
use anyhow::{anyhow, Result};
use std::{fmt, rc::Rc};

pub type LTerm = Rc<Term>;

#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    Variable(Symbol),
    Abstraction(Symbol, LTerm),
    Application(LTerm, LTerm),
}

pub fn eval(t: LTerm, env: &Env) -> Result<LTerm> {
    match t.as_ref() {
        Term::Application(t1, t2) => {
            let t1 = eval(t1.clone(), env)?;
            let t2 = eval(t2.clone(), env)?;
            match t1.as_ref() {
                Term::Abstraction(param, body) => eval(substitute(body, *param, t2), env),
                _ => panic!("Expected an abstraction"),
            }
        }
        Term::Variable(s) => env
            .get(*s)
            .ok_or_else(|| anyhow!("Variable `{}` is not bound", s)),
        _ => Ok(t),
    }
}

pub fn substitute(t: &LTerm, param: Symbol, arg: LTerm) -> LTerm {
    match t.as_ref() {
        // [param → arg]param
        Term::Variable(v) if *v == param => arg,
        // λp.body
        // [param → arg]body if p != param
        Term::Abstraction(p, body) if *p != param => {
            Rc::new(Term::Abstraction(*p, substitute(body, param, arg)))
        }
        // t1 t2
        // [param → arg]t1 [param → arg]t2
        Term::Application(t1, t2) => Rc::new(Term::Application(
            substitute(t1, param, arg.clone()),
            substitute(t2, param, arg),
        )),
        _ => t.clone(),
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Variable(v) => v.fmt(f),
            Term::Abstraction(p, b) => write!(f, "λ{}.{}", p, b),
            Term::Application(t1, t2) => {
                let (left_paren, right_paren) = if matches!(t1.as_ref(), Term::Abstraction(_, _)) {
                    ("(", ")")
                } else {
                    ("", "")
                };
                write!(f, "{}{}{} {}", left_paren, t1, right_paren, t2)
            }
        }
    }
}

impl From<&str> for Term {
    fn from(t: &str) -> Self {
        Term::Variable(t.into())
    }
}

#[macro_export]
macro_rules! T {
    (var $name:expr) => {
        Rc::new(Term::Variable($name.into()))
    };
    (abs $param:expr, $body:expr) => {
        Rc::new(Term::Abstraction($param.into(), $body.clone()))
    };
    (app $t1:expr, $t2:expr) => {
        Rc::new(Term::Application($t1.clone(), $t2.clone()))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(lt: LTerm, expected: LTerm) {
        actual_check(lt, expected, None);
    }

    fn check_env(lt: LTerm, expected: LTerm, env: &Env) {
        actual_check(lt, expected, Some(env));
    }

    fn actual_check(lt: LTerm, expected: LTerm, env: Option<&Env>) {
        let default_env = Env::new();
        let env = env.unwrap_or(&default_env);

        assert_eq!(eval(lt, &env).expect("Could not evaluate"), expected);
    }

    /// Evaluating a variable, returns the abstraction pointed to by the variable
    #[test]
    fn test_eval_variable() {
        let mut env = Env::new();
        let x = T![var "x"];
        let id = T![abs "x", x];
        env.insert("x", id.clone());

        check_env(T![var "x"], id, &env);
    }

    /// Evaluating an abstraction, returns the abstraction
    #[test]
    fn test_eval_abstraction() {
        let id = T![abs "x", T![var "x"]];
        check(id.clone(), id);
    }

    #[test]
    fn test_application_abstraction_to_abstraction() {
        let x = T![var "x"];
        // λx.x
        let id = T![abs "x", x];

        check(T![app id, id], id);
    }

    #[test]
    fn test_booleans() {
        let mut env = Env::new();
        // λt.λf.t
        let tru = T![abs "t", T![abs "f", T![var "t"]]];
        // λt.λf.f
        let fls = T![abs "t", T![abs "f", T![var "f"]]];
        // λb.λc. b c false
        let and =
            T![abs "b", T![abs "c", T![app T![app T![var "b"], T![var "c"]], T![var "false"]]]];

        env.insert("true", tru.clone());
        env.insert("false", fls.clone());
        env.insert("and", and.clone());

        // and true true → true
        check_env(T![app T![app and, tru], tru], tru.clone(), &env);
        // and true false → false
        check_env(T![app T![app and, tru], fls], fls.clone(), &env);
        // and false true → false
        check_env(T![app T![app and, fls], tru], fls.clone(), &env);
        // and false false → false
        check_env(T![app T![app and, fls], fls], fls.clone(), &env);

        // λb. b false true
        let not = T![abs "b", T![app T![app T![var "b"], fls], tru]];
        env.insert("not", not.clone());

        // not true → false
        check_env(T![app not, tru], fls.clone(), &env);
        // not false → true
        check_env(T![app not, fls], tru.clone(), &env);

        // λb.λc. b true c
        let or = T![abs "b", T![abs "c", T![app T![app T![var "b"], T![var "true"]], T![var "c"]]]];
        env.insert("not", not);

        // or true true → true
        check_env(T![app T![app or, tru], tru], tru.clone(), &env);
        // or true false → true
        check_env(T![app T![app or, tru], fls], tru.clone(), &env);
        // or false true → true
        check_env(T![app T![app or, fls], tru], tru, &env);
        // or false false → false
        check_env(T![app T![app or, fls], fls], fls, &env);
    }
}
