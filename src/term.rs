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
use crate::env::Env;
use crate::Symbol;
use crate::T;
use anyhow::{anyhow, Result};
use std::rc::Rc;

pub type LTerm = Rc<Term>;

#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    /// x
    Variable(/** de Bruijn index */ usize),
    /// λx.t
    Abstraction(/** Original name of the parameter */ Symbol, LTerm),
    /// t t
    Application(LTerm, LTerm),
}

/// Reduce a term using the call-by-value strategy.
pub fn eval(t: LTerm, env: &Env) -> Result<LTerm> {
    // rm_names(&t, &env)?;
    eval_(t, env)
}

/// ```text
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
/// (λ.t12)v2 → ↑⁻¹([0 → ↑¹(v2)]t12)    (E-AppAbs)
/// ```
fn eval_(t: LTerm, env: &Env) -> Result<LTerm> {
    match t.as_ref() {
        Term::Application(t1, t2) => {
            //    t1 → t1'
            // --------------
            // t1 t2 → t1' t2
            // If t1 can be evaluated, it is evaluated first
            // E-App1
            let v1 = eval_(t1.clone(), env)?;
            //    t2 → t2'
            // --------------
            // v1 t2 → v1' t2'
            // Once t1 is a value which can no longer be evaluated
            // We evaluate t2
            // E-App2
            let v2 = eval_(t2.clone(), env)?;
            match v1.as_ref() {
                // E-AppAbs
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
                _ => Err(anyhow!(
                    "Expected an abstraction, got {}",
                    term_to_string(t1, &env)?
                )),
            }
        }
        Term::Variable(idx) => env
            .get_from_db_index(*idx)
            .ok_or_else(|| anyhow!("Invalid de Bruijn index: {}", idx)),
        // Evaluating an abstraction, yields the abstraction itself.
        _ => Ok(t),
    }
}

/// The substitution of a term `s` for variable number `j` in a term `t`,
/// written [j → s]t, is defined as follows:
///
/// ```text
/// [j → s]k = s if k = j
/// [j → s]k = k otherwise
/// [j → s](λ.t1) = λ.[j+1 → ↑¹(s)]t1
/// [j → s](t1 t2) = ([j → s]t1 [j → s]t2)
/// ```
pub fn substitute(t: &LTerm, db_idx: usize, arg: LTerm) -> Result<LTerm> {
    match t.as_ref() {
        Term::Variable(idx) => match *idx {
            // [j → s]k = s if k = j
            idx if idx == db_idx => Ok(arg),
            // [j → s]k = k otherwise
            _ => Ok(t.clone()),
        },
        // [j → s](λ.t1) = λ.[j+1 → ↑¹(s)]t1
        Term::Abstraction(v, body) => Ok(T![
            abs * v,
            substitute(body, db_idx + 1, shift(arg, 1, 0)?)?
        ]),
        // [j → s](t1 t2) = ([j → s]t1 [j → s]t2)
        Term::Application(t1, t2) => Ok(T![app
            substitute(t1, db_idx, arg.clone())?,
            substitute(t2, db_idx, arg)?,
        ]),
    }
}

/// The _d_-place shift of a term `t` above cutoff `c`, written here
/// as ↑[d,c](t), is defined as follows:
///
/// ```text
/// ↑[d,c](k) = k if k < c
/// ↑[d,c](k) = k + d if k ≥ c
/// ↑[d,c](λ.t1) = λ.↑[d,c+1]t1
/// ↑[d,c](t1 t2) = ↑[d,c](t1) ↑[d,c](t2)
/// ```
fn shift(t: LTerm, d_place: isize, cutoff: usize) -> Result<LTerm> {
    match t.as_ref() {
        Term::Variable(idx) => match *idx {
            // ↑[d,c](k) = k if k < c
            idx if idx < cutoff => Ok(t),
            // ↑[d,c](k) = k + d if k ≥ c
            idx => {
                use std::convert::TryFrom;
                let new_idx = usize::try_from(isize::try_from(idx)? + d_place)?;
                Ok(T![var new_idx])
            }
        },
        // ↑[d,c](λ.t1) = λ.↑[d,c+1]t1
        Term::Abstraction(var, body) => {
            Ok(T![abs * var, shift(body.clone(), d_place, cutoff + 1)?])
        }
        // ↑[d,c](t1 t2) = ↑[d,c](t1) ↑[d,c](t2)
        Term::Application(t1, t2) => {
            let t1 = shift(t1.clone(), d_place, cutoff)?;
            let t2 = shift(t2.clone(), d_place, cutoff)?;
            Ok(T![app t1, t2])
        }
    }
}

pub fn term_to_string(t: &LTerm, env: &Env) -> Result<String> {
    match t.as_ref() {
        Term::Variable(idx) => match env.get_name_from_db_index(*idx) {
            Some(v) => Ok(v.to_string()),
            None => Err(anyhow!("Invalid de Bruijn index: {}", *idx)),
        },
        Term::Abstraction(param, body) => {
            let (param, env) = new_name(*param, &env);
            Ok(format!("λ{}.{}", param, term_to_string(body, &env)?))
        }
        Term::Application(t1, t2) => {
            let t1_paren = matches!(**t1, Term::Abstraction(_, _));
            let t2_paren = matches!(**t2, Term::Application(_, _));
            let (t2_lp, t2_rp) = if t2_paren { ("(", ")") } else { ("", "") };
            let (t1_lp, t1_rp) = if t1_paren { ("(", ")") } else { ("", "") };
            Ok(format!(
                "{}{}{} {}{}{}",
                t1_lp,
                term_to_string(t1, &env)?,
                t1_rp,
                t2_lp,
                term_to_string(t2, &env)?,
                t2_rp
            ))
        }
    }
}

fn new_name<'a>(s: impl Into<Symbol>, env: &'a Env) -> (Symbol, Env<'a>) {
    let mut current_symbol = s.into();
    while env.get_db_index(current_symbol).is_some() {
        current_symbol = Symbol::from(format!("{}'", current_symbol));
    }
    let mut new_env = Env::with_parent(&env);
    new_env.insert_local(current_symbol);
    (current_symbol, new_env)
}

#[macro_export]
macro_rules! T {
    (var $n:expr $(,)?) => {
        Rc::new(Term::Variable($n))
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
        assert_eq!(eval_res, expected);
    }

    /// Evaluating a variable, returns the abstraction pointed to by the variable
    #[test]
    fn test_eval_variable() -> Result<()> {
        let mut env = Env::new();
        let id = parse("λx.x", &env)?;
        env.insert_variable("id", id.clone());

        check_env(parse("id", &env)?, id, &env);
        Ok(())
    }

    /// Evaluating an abstraction, returns the abstraction
    #[test]
    fn test_eval_abstraction() -> Result<()> {
        let id = parse("λx.x", &Env::new())?;
        check(id.clone(), id);
        Ok(())
    }

    #[test]
    fn test_application_abstraction_to_abstraction() -> Result<()> {
        let id = parse("λx.x", &Env::new())?;
        let mut env = Env::new();
        env.insert_variable("id", id.clone());

        check_env(parse("id id", &env)?, id, &env);
        Ok(())
    }

    #[test]
    fn test_booleans() -> Result<()> {
        let mut env = Env::new();
        let tru = parse("λt.λf.t", &env)?;
        env.insert_variable("true", tru.clone());
        // λt.λf.f
        let fls = parse("λt.λf.f", &env)?;
        env.insert_variable("false", fls.clone());
        // λb.λc. b c false
        let and = parse("λb.λc.b c false", &env)?;
        env.insert_variable("and", and.clone());

        // and true true → true
        check_env(parse("and true true", &env)?, tru.clone(), &env);
        // and true false → false
        check_env(parse("and true false", &env)?, fls.clone(), &env);
        // and false true → false
        check_env(parse("and false true", &env)?, fls.clone(), &env);
        // and false false → false
        check_env(parse("and false false", &env)?, fls.clone(), &env);

        // λb. b false true
        let not = parse("λb. b false true", &env)?;
        env.insert_variable("not", not.clone());

        // not true → false
        check_env(parse("not true", &env)?, fls.clone(), &env);
        // not false → true
        check_env(parse("not false", &env)?, tru.clone(), &env);

        // λb.λc. b true c
        let or = parse("λb.λc.b true c", &env)?;
        env.insert_variable("or", or.clone());

        // or true true → true
        check_env(parse("or true true", &env)?, tru.clone(), &env);
        // or true false → true
        check_env(parse("or true false", &env)?, tru.clone(), &env);
        // or false true → true
        check_env(parse("or false true", &env)?, tru.clone(), &env);
        // or false false → false
        check_env(parse("or false false", &env)?, fls.clone(), &env);
        Ok(())
    }

    #[test]
    fn test_shifting() -> Result<()> {
        let mut env = Env::new();
        let tru = parse("λt.λf.t", &env)?;
        env.insert_variable("true", tru.clone());

        let id = parse("λx.x", &env)?;
        env.insert_variable("id", id.clone());

        let id_shifted = shift(id.clone(), 1, 0).expect("Couldn't shift term");
        // Shouldn't touch id
        assert_eq!(id_shifted, id);

        let r#const = parse("λx.true", &env)?;
        let const_shifted = shift(r#const.clone(), 1, 0).expect("Couldn't shift term");
        // Should shift true from 1 → 2
        assert_eq!(const_shifted, T![abs "x", T![var 2]]);

        let test = parse("true id", &env)?;
        let test_shifted = shift(test.clone(), 3, 1).expect("Couldn't shift term");
        assert_eq!(test_shifted, T![app T![var 0], T![var 4]]);
        assert_eq!(test, T![app T![var 0], T![var 1]]);

        // ↑²(λ.λ.1 (0 2))
        let book_example_1 = parse("λx.λy.x (y true)", &env)?;
        let b_ex_1_shifted = shift(book_example_1.clone(), 2, 0).expect("Couldn't shift term");
        // Expected λ.λ.1 (0 4)
        assert_eq!(
            b_ex_1_shifted,
            T![abs "x", T![abs "y", T![app T![var 1], T![app T![var 0], T![var 4]]]]]
        );

        // ↑²(λ.0 1 (λ. 0 1 2))
        let book_example_2 = parse("λx.x true (λy.y x true)", &env)?;
        let b_ex_2_shifted = shift(book_example_2.clone(), 2, 0).expect("Couldn't shift term");
        // Expected λ.0 3 (λ. 0 1 4)
        assert_eq!(
            b_ex_2_shifted,
            T![abs "x", T![app T![app T![var 0], T![var 3]], T![abs "y", T![app T![app T![var 0], T![var 1]], T![var 4]]]]]
        );
        Ok(())
    }

    #[test]
    fn test_de_bruijn_indices_work() -> Result<()> {
        let mut env = Env::new();
        let t = parse("λt.λf.t", &env)?;
        assert_eq!(term_to_string(&t, &env)?, "λt.λf.t");

        let t = parse("λx.x x", &env)?;
        assert_eq!(term_to_string(&t, &env)?, "λx.x x");

        let t = parse("λx.λx.x", &env)?;
        assert_eq!(term_to_string(&t, &env)?, "λx.λx'.x'");

        let t = parse("(λx.λy.x y) λx.x", &env)?;
        let t = eval(t, &env)?;
        assert_eq!(term_to_string(&t, &env)?, "λy.(λx.x) y");

        let id = parse("λx.x", &env)?;
        env.insert_variable("id", id);

        let t = parse("(λz.λid.id z) λz.id z", &env)?;
        let t = eval(t, &env)?;
        assert_eq!(term_to_string(&t, &env)?, "λid'.id' λz.id z");
        Ok(())
    }
}
