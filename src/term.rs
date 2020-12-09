use crate::env::{Env, TermWithIndex};
use crate::Symbol;
use crate::T;
use anyhow::{anyhow, Result};
use std::{cell::Cell, fmt, rc::Rc};

pub type LTerm = Rc<Term>;

#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    Variable(Symbol, Cell<Option<usize>>),
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
                _ => Err(anyhow!("Expected an abstraction, got {}", t1)),
            }
        }
        Term::Variable(s, _) => env
            .get(*s)
            .ok_or_else(|| anyhow!("Variable `{}` is not bound", s)),
        _ => Ok(t),
    }
}

pub fn substitute(t: &LTerm, param: Symbol, arg: LTerm) -> LTerm {
    match t.as_ref() {
        // [param → arg]param
        Term::Variable(v, _) if *v == param => arg,
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

/// Traverse over the Lterm and set all the variables' de Bruijn index.
pub fn rm_names(t: &LTerm, env: &Env) -> Result<()> {
    match t.as_ref() {
        Term::Variable(var, idx) => match env.get_with_calculated_db_index(*var) {
            Some(TermWithIndex { db_idx, .. }) => {
                idx.set(Some(db_idx));
                Ok(())
            }
            None => Err(anyhow!("The variable `{}` is not bound", var)),
        },
        Term::Abstraction(var, body) => {
            let mut env = Env::with_parent(&env);
            // FIXME: Create a new env for the db_idx calculation
            env.insert(*var, T![var * var]);
            rm_names(body, &env)
        }
        Term::Application(t1, t2) => {
            rm_names(t1, env)?;
            rm_names(t2, env)
        }
    }
}

fn shift(t: LTerm, d_place: usize, cutoff: usize) -> Result<LTerm> {
    match t.as_ref() {
        Term::Variable(v, idx) => match idx.get() {
            Some(idx) if idx < cutoff => Ok(t),
            Some(idx) => Ok(T![var * v, idx + d_place]),
            None => Err(anyhow!("Tried to shift a variable with no de Bruijn index")),
        },
        Term::Abstraction(var, body) => {
            Ok(T![abs * var, shift(body.clone(), d_place, cutoff + 1)?])
        }
        Term::Application(t1, t2) => {
            let t1 = shift(t1.clone(), d_place, cutoff)?;
            let t2 = shift(t2.clone(), d_place, cutoff)?;
            Ok(T![app t1, t2])
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Variable(v, _) => v.fmt(f),
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
        Term::Variable(t.into(), Cell::new(None))
    }
}

#[macro_export]
macro_rules! T {
    (var $name:expr, $n:expr) => {
        Rc::new(Term::Variable($name.into(), Some($n).into()))
    };
    (var $name:expr) => {
        Rc::new(Term::Variable($name.into(), None.into()))
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

    #[test]
    fn test_basic_rm_names() {
        let env = Env::new();
        let x = T![var "x"];
        let id = T![abs "x", x];
        rm_names(&id, &env).expect("Could not remove names");
        assert_eq!(x, T![var "x", 0]);
    }

    #[test]
    fn test_rm_names_selects_the_closest_binding() {
        let env = Env::new();
        let id = T![abs "x", T![abs "x", T![var "x"]]];
        rm_names(&id, &env).expect("Could not remove names");
        assert_eq!(id, T![abs "x", T![abs "x", T![var "x", 0]]]);
    }

    #[test]
    fn test_rm_names_variable_not_bound() {
        let env = Env::new();
        let id = T![abs "x", T![var "y"]];
        assert_eq!(
            rm_names(&id, &env)
                .expect_err("Could not remove names")
                .to_string(),
            "The variable `y` is not bound"
        );
    }

    #[test]
    fn test_rm_names() {
        let mut env = Env::new();
        let tru = T![abs "t", T![abs "f", T![var "t"]]];
        rm_names(&tru, &env).expect("Could not remove names");
        assert_eq!(tru, T![abs "t", T![abs "f", T![var "t", 1]]]);
        env.insert("true", tru);

        let fls = T![abs "t", T![abs "f", T![var "f"]]];
        rm_names(&fls, &env).expect("Could not remove names");
        assert_eq!(fls, T![abs "t", T![abs "f", T![var "f", 0]]]);
        env.insert("false", fls);

        let and =
            T![abs "b", T![abs "c", T![app T![app T![var "b"], T![var "c"]], T![var "false"]]]];
        rm_names(&and, &env).expect("Could not remove names");
        assert_eq!(
            and,
            T![abs "b", T![abs "c", T![app T![app T![var "b", 1], T![var "c", 0]], T![var "false", 3]]]]
        );
        env.insert("and", and);
    }

    #[test]
    fn test_shifting() {
        let id = T![abs "x", T![var "x", 0]];

        let id_shifted = shift(id.clone(), 1, 0).expect("Couldn't shift term");
        // Shouldn't touch id
        assert_eq!(id_shifted, id);

        let r#const = T![abs "x", T![var "true", 1]];
        let const_shifted = shift(r#const, 1, 0).expect("Couldn't shift term");
        // Should shift true from 1 → 2
        assert_eq!(const_shifted, T![abs "x", T![var "true", 2]]);

        let test = T![app T![var "x", 0], T![var "y", 1]];
        let test_shifted = shift(test, 3, 1).expect("Couldn't shift term");
        // Should shift true from 1 → 2
        assert_eq!(test_shifted, T![app T![var "x", 0], T![var "y", 4]]);
    }
}
