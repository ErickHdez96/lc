/// Evaluation strategies:
///
/// Given the following expression:
///
/// `(λx.x) ((λx.x) (λz. (λx.x) z))`
///
/// Which can be written more readably as:
///
/// `id (id (λz. id z))`
///
/// ## Full β-reduction
///
/// Any redex (reducible expression) may be reduced at any time.
///
/// ```text
///     id (id (λz. --> id z <--))
/// →   id (--> id (λz.z) <--)
/// →   -->id (λz.z)<--
/// →   λz.z
/// ↛
/// ```
///
/// ## Normal order
///
/// The leftmost, outermos redex is always reduced first.
///
/// ```text
///     --> id (id (λz. id z)) <--
/// →   --> id (λz. id z) <--
/// →   λz. --> id z <--
/// →   λz.z
/// ↛
/// ```
///
/// ## Call by name
///
/// Similar to _Normal order_, but it does not allow reductions inside abstractions.
///
/// ```text
///     --> id (id (λz. id z)) <--
/// →   --> id (λz. id z) <--
/// →   λz. id z
/// ↛
/// ```
///
/// ## Call by value
///
/// Only outermost redexes are reduced _and_ a redex is reduced only when its
/// right-hand side has already been reduced to a _value_ (a term that is finished
/// computing and cannot be reduced any further).
///
/// ```text
///     id --> (id (λz. id z)) <--
/// →   --> id (λz. id z) <--
/// →   λz. id z
/// ↛
/// ```
///
/// Call-by-value is _strict_, in the sense that the arguments to functions are always evaluated,
/// whether or not they are used by the body of the function.
///
/// _Non-strict_ (or _lazy) strategies (e.g. call-by-name, call-by-need) evaluate only the
/// arguments that are actually used.
///
/// Here call by value is used.
use crate::env::{Env, TermWithIndex};
use crate::Symbol;
use crate::T;
use anyhow::{anyhow, Result};
use std::{cell::Cell, fmt, rc::Rc};

pub type LTerm = Rc<Term>;

#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    /// x
    Variable(Symbol, Cell<Option<usize>>),
    /// λx.t
    Abstraction(Symbol, LTerm),
    /// t t
    Application(LTerm, LTerm),
}

pub fn eval(t: LTerm, env: &Env) -> Result<LTerm> {
    rm_names(&t, &env)?;
    eval_(t, env)
}

/// t ::=                   Terms:
///     x                       Variable
///     λx.t                    Abstraction
///     t t                     Application
///
/// v ::=                   Values:
///     λx.t                    Abstraction Value
///
///    t1 → t1'
/// --------------              E-App1
/// t1 t2 → t1' t2
///
///    t2 → t2'
/// --------------              E-App2
/// v1 t2 → v1 t2'
///
/// (λx.t12)v2 → [x → v2]t12    (E-AppAbs)
fn eval_(t: LTerm, env: &Env) -> Result<LTerm> {
    match t.as_ref() {
        Term::Application(t1, t2) => {
            //    t1 → t1'
            // --------------
            // t1 t2 → t1' t2
            // If t1 can be evaluated, it is evaluated first
            let v1 = eval_(t1.clone(), env)?;
            //    t2 → t2'
            // --------------
            // v1 t2 → v1' t2'
            // Once t1 is a value which can no longer be evaluated
            // We evaluate t2
            let v2 = eval_(t2.clone(), env)?;
            match v1.as_ref() {
                // (λ.t12)v2 → ↑⁻¹([0 → ↑¹(v2)]t12)
                Term::Abstraction(_, body) => {
                    // s_v2 = ↑¹(v2)
                    let shifted_v2 = shift(v2, 1, 0)?;
                    // sub = [0 → s_v2]t12
                    let substitution = substitute(body, 0, shifted_v2)?;
                    // shi = ↑⁻¹sub
                    let shifted = shift(substitution, -1, 0)?;
                    let evaluation = eval_(shifted, &env)?;
                    Ok(evaluation)
                }
                _ => Err(anyhow!("Expected an abstraction, got {}", t1)),
            }
        }
        Term::Variable(v, idx) => idx
            .get()
            .and_then(|idx| env.get_from_db_index(idx))
            .ok_or_else(|| anyhow!("Variable `{}` is not bound", v)),
        // An abstraction cannot be evaluated
        _ => Ok(t),
    }
}

pub fn substitute(t: &LTerm, db_idx: usize, arg: LTerm) -> Result<LTerm> {
    match t.as_ref() {
        Term::Variable(v, idx) => match idx.get() {
            // [db_idx → arg]t = arg if idx = db_idx
            Some(idx) if idx == db_idx => Ok(arg),
            // [db_idx → arg]t = t otherwise
            Some(_) => Ok(t.clone()),
            None => Err(anyhow!(
                "Could not substitute: Variable `{}` is not bound",
                v
            )),
        },
        // [db_idx → arg](λ.t1) = λ.[db_idx+1 → ↑¹(arg)]t1
        Term::Abstraction(v, body) => Ok(T![
            abs * v,
            substitute(body, db_idx + 1, shift(arg, 1, 0)?)?
        ]),
        // [db_idx → arg](t1 t2) = ([db_idx → arg]t1 [db_idx → arg]t2)
        Term::Application(t1, t2) => Ok(T![app
            substitute(t1, db_idx, arg.clone())?,
            substitute(t2, db_idx, arg)?,
        ]),
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

fn shift(t: LTerm, d_place: isize, cutoff: usize) -> Result<LTerm> {
    match t.as_ref() {
        Term::Variable(v, idx) => match idx.get() {
            Some(idx) if idx < cutoff => Ok(t),
            Some(idx) => Ok(T![var * v, (idx as isize + d_place) as usize]),
            None => Err(anyhow!(
                "Tried to shift a variable with no de Bruijn index, `{}`",
                v
            )),
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
    (var $name:expr, $n:expr $(,)?) => {
        Rc::new(Term::Variable($name.into(), Some($n).into()))
    };
    (var $name:expr $(,)?) => {
        Rc::new(Term::Variable($name.into(), None.into()))
    };
    (abs $param:expr, $body:expr $(,)?) => {
        Rc::new(Term::Abstraction($param.into(), $body.clone()))
    };
    (app $t1:expr, $t2:expr $(,)?) => {
        Rc::new(Term::Application($t1.clone(), $t2.clone()))
    };
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

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

        let eval_res = eval(lt, &env).expect("Could not evaluate");
        println!("{}", eval_res);
        assert_eq!(eval_res, expected);
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
        let tru = parse("λt.λf.t").expect("Could not parse");
        // λt.λf.f
        let fls = parse("λt.λf.f").expect("Could not parse");
        // λb.λc. b c false
        let and = parse("λb.λc.b c false").expect("Could not parse");

        rm_names(&tru, &env).unwrap();
        env.insert("true", tru.clone());
        rm_names(&fls, &env).unwrap();
        env.insert("false", fls.clone());
        rm_names(&and, &env).unwrap();
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
        let not = parse("λb. b false true").expect("Could not parse");
        rm_names(&not, &env).unwrap();
        env.insert("not", not.clone());

        // not true → false
        check_env(T![app not, tru], fls.clone(), &env);
        // not false → true
        check_env(T![app not, fls], tru.clone(), &env);

        // λb.λc. b true c
        let or = T![abs "b", T![abs "c", T![app T![app T![var "b"], T![var "true"]], T![var "c"]]]];
        rm_names(&or, &env).unwrap();
        env.insert("or", or.clone());

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
        let const_shifted = shift(r#const.clone(), 1, 0).expect("Couldn't shift term");
        // Should shift true from 1 → 2
        assert_eq!(const_shifted, T![abs "x", T![var "true", 2]]);
        // Shouldn't modify const
        assert_eq!(r#const, T![abs "x", T![var "true", 1]]);

        let test = T![app T![var "x", 0], T![var "y", 1]];
        let test_shifted = shift(test.clone(), 3, 1).expect("Couldn't shift term");
        assert_eq!(test_shifted, T![app T![var "x", 0], T![var "y", 4]]);
        assert_eq!(test, T![app T![var "x", 0], T![var "y", 1]]);

        // ↑²(λ.λ.1 (0 2))
        let book_example_1 = T![abs "x", T![abs "y", T![app T![var "x", 1], T![app T![var "y", 0], T![var "true", 2]]]]];
        let b_ex_1_shifted = shift(book_example_1.clone(), 2, 0).expect("Couldn't shift term");
        // Expected λ.λ.1 (0 4)
        assert_eq!(
            b_ex_1_shifted,
            T![abs "x", T![abs "y", T![app T![var "x", 1], T![app T![var "y", 0], T![var "true", 4]]]]]
        );
        // Shouldn't modify book_example_1
        assert_eq!(
            book_example_1,
            T![abs "x", T![abs "y", T![app T![var "x", 1], T![app T![var "y", 0], T![var "true", 2]]]]]
        );

        // ↑²(λ.0 1 (λ. 0 1 2))
        let book_example_2 = T![abs "x", T![app T![app T![var "x", 0], T![var "true", 1]], T![abs "y", T![app T![app T![var "y", 0], T![var "x", 1]], T![var "true", 2]]]]];
        let b_ex_2_shifted = shift(book_example_2.clone(), 2, 0).expect("Couldn't shift term");
        // Expected λ.0 3 (λ. 0 1 4)
        assert_eq!(
            b_ex_2_shifted,
            T![abs "x", T![app T![app T![var "x", 0], T![var "true", 3]], T![abs "y", T![app T![app T![var "y", 0], T![var "x", 1]], T![var "true", 4]]]]]
        );
        // Shouldn't modify book_example_2
        assert_eq!(
            book_example_2,
            T![abs "x", T![app T![app T![var "x", 0], T![var "true", 1]], T![abs "y", T![app T![app T![var "y", 0], T![var "x", 1]], T![var "true", 2]]]]]
        );
    }

    #[test]
    fn test_de_bruijn_indices_work() {}
}
