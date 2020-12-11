use crate::types::LTy;
use crate::Symbol;
use crate::T;
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
use crate::{env::Env, types::type_of};
use anyhow::{anyhow, Result};
use std::convert::TryFrom;
use std::rc::Rc;

pub type LTerm = Rc<Term>;

/// ```text
/// terms:
///     x                   Variable
///     λx:T.t              Abstraction
///     t t                 Application
///     true                Constant true
///     false               Constant false
///     if t then t else t  If
///     0                   Constant zero
///     succ t              Successor
///     pred t              Predecessor
///     iszero t            zero test
///     unit                constant unit
/// ```
#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    /// x
    Variable(/** de Bruijn index */ usize),
    /// λx.t
    Abstraction(/** Original name of the parameter */ Symbol, LTy, LTerm),
    /// t t
    Application(LTerm, LTerm),
    True,
    False,
    If(LTerm, LTerm, LTerm),
    Zero,
    Succ(LTerm),
    Pred(LTerm),
    IsZero(LTerm),
    Unit,
}

/// ```text
/// t ::=                           Terms:
///     x                               Variable
///     λx.t                            Abstraction
///     t t                             Application
///
/// v ::=                           Values:
///     λx.t                            Abstraction Value
///
///    t1 → t1'
/// --------------                      E-App1
/// t1 t2 → t1' t2
///
///    t2 → t2'
/// --------------                      E-App2
/// v1 t2 → v1 t2'
///
/// (λ.t12)v2 → ↑⁻¹([0 → ↑¹(v2)]t12)    (E-AppAbs)
/// ```
pub fn eval(t: &LTerm, env: &Env) -> Result<LTerm> {
    type_of(&t, &env)?;
    eval_(&t, env)
}

fn eval_(t: &LTerm, env: &Env) -> Result<LTerm> {
    match t.as_ref() {
        Term::Application(t1, t2) => {
            //    t1 → t1'
            // --------------
            // t1 t2 → t1' t2
            // If t1 can be evaluated, it is evaluated first
            // E-App1
            let v1 = eval_(t1, env)?;
            //    t2 → t2'
            // --------------
            // v1 t2 → v1' t2'
            // Once t1 is a value which can no longer be evaluated
            // We evaluate t2
            // E-App2
            let v2 = eval_(t2, env)?;
            match v1.as_ref() {
                // E-AppAbs
                // (λ.t12)v2 → ↑⁻¹([0 → ↑¹(v2)]t12)
                Term::Abstraction(_, _, body) => {
                    // s_v2 = ↑¹(v2)
                    let shifted_v2 = shift(&v2, 1)?;
                    // sub = [0 → s_v2]t12
                    let substitution = substitute(body, 0, shifted_v2)?;
                    // shi = ↑⁻¹sub
                    let shifted = shift(&substitution, -1)?;
                    let evaluation = eval_(&shifted, &env)?;
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
        Term::If(cond, then, else_b) => {
            let cond = eval_(cond, &env)?;

            match cond.as_ref() {
                Term::True => eval_(then, &env),
                Term::False => eval_(else_b, &env),
                _ => Err(anyhow!(
                    "Expected a boolean, got `{}`",
                    term_to_string(&cond, &env)?
                )),
            }
        }
        Term::Abstraction(_, _, _) | Term::True | Term::False | Term::Zero | Term::Unit => {
            Ok(t.clone())
        }
        Term::Succ(t) => Ok(T![succ eval_(t, &env)?]),
        Term::Pred(t) => {
            let t = eval_(t, &env)?;
            match t.as_ref() {
                Term::Zero => Ok(T![0]),
                Term::Succ(t) => Ok(t.clone()),
                _ => Err(anyhow!(
                    "Expected a numeric value, got `{}`",
                    term_to_string(&t, &env)?
                )),
            }
        }
        Term::IsZero(t) => {
            let t = eval_(t, &env)?;
            match t.as_ref() {
                Term::Zero => Ok(T![true]),
                Term::Succ(_) => Ok(T![false]),
                _ => Err(anyhow!(
                    "Expected a numeric value, got `{}`",
                    term_to_string(&t, &env)?
                )),
            }
        }
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
fn substitute(t: &LTerm, db_idx: usize, arg: LTerm) -> Result<LTerm> {
    term_map(t, 0, |idx, c| {
        if idx == c + db_idx {
            shift(&arg, isize::try_from(c)?)
        } else {
            Ok(T![var idx])
        }
    })
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
fn shift_above(t: &LTerm, d_place: isize, cutoff: usize) -> Result<LTerm> {
    term_map(t, cutoff, |idx, c| {
        Ok(if idx >= c {
            let new_idx = usize::try_from(isize::try_from(idx)? + d_place)?;
            T![var new_idx]
        } else {
            T![var idx]
        })
    })
}

fn shift(t: &LTerm, d_place: isize) -> Result<LTerm> {
    shift_above(t, d_place, 0)
}

fn term_map<F>(t: &LTerm, cutoff: usize, on_var: F) -> Result<LTerm>
where
    F: Fn(usize, usize) -> Result<LTerm>,
{
    fn map<F: Fn(usize, usize) -> Result<LTerm>>(
        t: &LTerm,
        cutoff: usize,
        on_var: &F,
    ) -> Result<LTerm> {
        match t.as_ref() {
            Term::Variable(idx) => on_var(*idx, cutoff),
            Term::Abstraction(v, ty, body) => Ok(T![abs(*v), ty, map(body, cutoff + 1, on_var)?]),
            Term::Application(t1, t2) => {
                Ok(T![app map(t1, cutoff, on_var)?, map(t2, cutoff, on_var)?])
            }
            Term::True | Term::False | Term::Zero | Term::Unit => Ok(t.clone()),
            Term::Succ(t) => Ok(T![succ map(t, cutoff, on_var)?]),
            Term::Pred(t) => Ok(T![pred map(t, cutoff, on_var)?]),
            Term::IsZero(t) => Ok(T![iszero map(t, cutoff, on_var)?]),
            Term::If(cond, then, else_b) => Ok(T![if
                                               map(cond, cutoff, on_var)?,
                                               map(then, cutoff, on_var)?,
                                               map(else_b, cutoff, on_var)?,
            ]),
        }
    }
    map(t, cutoff, &on_var)
}

pub fn term_to_string(t: &LTerm, env: &Env) -> Result<String> {
    match t.as_ref() {
        Term::Variable(idx) => match env.get_name_from_db_index(*idx) {
            Some(v) => Ok(v.to_string()),
            None => Err(anyhow!("Invalid de Bruijn index: {}", *idx)),
        },
        Term::Abstraction(param, ty, body) => {
            let (param, env) = new_name(*param, ty, &env);
            Ok(format!("λ{}:{}.{}", param, ty, term_to_string(body, &env)?))
        }
        Term::Application(t1, t2) => {
            let t1_paren = matches!(**t1, Term::Abstraction(_, _, _));
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
        Term::Unit => Ok(String::from("unit")),
        Term::True => Ok(String::from("true")),
        Term::False => Ok(String::from("false")),
        Term::Zero => Ok(String::from("0")),
        Term::Pred(t) => Ok(format!("pred {}", term_to_string(t, &env)?)),
        Term::Succ(t) => Ok(format!("succ {}", term_to_string(t, &env)?)),
        Term::IsZero(t) => Ok(format!("iszero {}", term_to_string(t, &env)?)),
        Term::If(c, t, e) => Ok(format!(
            "if {} then {} else {}",
            term_to_string(c, &env)?,
            term_to_string(t, &env)?,
            term_to_string(e, &env)?,
        )),
    }
}

fn new_name<'a>(s: impl Into<Symbol>, ty: &LTy, env: &'a Env) -> (Symbol, Env<'a>) {
    let mut current_symbol = s.into();
    while env.get_db_index(current_symbol).is_some() {
        current_symbol = Symbol::from(format!("{}'", current_symbol));
    }
    let mut new_env = Env::with_parent(&env);
    new_env.insert_local(current_symbol, ty.clone());
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
    (abs $param:expr, $ty:expr, $body:expr $(,)?) => {
        Rc::new(Term::Abstraction($param.into(), $ty.clone(), $body.clone()))
    };
    (app $t1:expr, $t2:expr $(,)?) => {
        Rc::new(Term::Application($t1.clone(), $t2.clone()))
    };
    (true $(,)?) => {
        Rc::new(Term::True)
    };
    (false $(,)?) => {
        Rc::new(Term::False)
    };
    (if $cond:expr, $then:expr, $else:expr $(,)?) => {
        Rc::new(Term::If($cond.clone(), $then.clone(), $else.clone()))
    };
    (0) => {
        Rc::new(Term::Zero)
    };
    (succ $t:expr) => {
        Rc::new(Term::Succ($t.clone()))
    };
    (pred $t:expr) => {
        Rc::new(Term::Pred($t.clone()))
    };
    (iszero $t:expr) => {
        Rc::new(Term::IsZero($t.clone()))
    };
    (unit) => {
        Rc::new(Term::Unit)
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Ty;
    use crate::{parser::parse, types::type_of, TY};
    use std::rc::Rc;

    fn check_parse(input: &str, expected: LTerm) {
        let env = Env::new();
        actual_check(parse(input, &env).expect("Couldn't parse"), expected, &env);
    }

    fn check(lt: LTerm, expected: LTerm) {
        actual_check(lt, expected, &Env::new());
    }

    fn check_env(lt: LTerm, expected: LTerm, env: &Env) {
        actual_check(lt, expected, env);
    }

    fn actual_check(lt: LTerm, expected: LTerm, env: &Env) {
        let eval_res = eval(&lt, &env).expect("Could not evaluate");
        assert_eq!(eval_res, expected);
    }

    /// Evaluating a variable, returns the abstraction pointed to by the variable
    #[test]
    fn test_eval_variable() -> Result<()> {
        let mut env = Env::new();
        let id = parse("λx:Bool.x", &env)?;
        env.insert_variable("id", id.clone(), type_of(&id, &env)?);

        check_env(parse("id", &env)?, id, &env);
        Ok(())
    }

    /// Evaluating an abstraction, returns the abstraction
    #[test]
    fn test_eval_abstraction() -> Result<()> {
        let id = parse("λx:Bool.x", &Env::new())?;
        check(id.clone(), id);
        Ok(())
    }

    #[test]
    fn test_application_abstraction_to_abstraction() -> Result<()> {
        let mut env = Env::new();
        let id = parse("λx:Bool.x", &env)?;
        let apply_fn = parse("λf:Bool → Bool.λb:Bool.f b", &env)?;
        env.insert_variable("id", id.clone(), type_of(&id, &env)?);
        env.insert_variable("applyfn", apply_fn.clone(), type_of(&apply_fn, &env)?);

        check_env(
            parse("applyfn id", &env)?,
            parse("λb:Bool.(λx:Bool.x) b", &env)?,
            &env,
        );
        Ok(())
    }

    #[test]
    fn test_booleans() -> Result<()> {
        let mut env = Env::new();
        let tru = parse("λt:Bool.λf:Bool.t", &env)?;
        env.insert_variable("tru", tru.clone(), type_of(&tru, &env)?);
        // λt.λf.f
        let fls = parse("λt:Bool.λf:Bool.f", &env)?;
        env.insert_variable("fls", fls.clone(), type_of(&fls, &env)?);
        // λb.λc. b c false
        let and = parse("λb:Bool.λc:Bool.if b then c else false", &env)?;
        env.insert_variable("and", and.clone(), type_of(&and, &env)?);

        // and true true → true
        check_env(parse("and true true", &env)?, T![true], &env);
        // and true false → false
        check_env(parse("and true false", &env)?, T![false], &env);
        // and false true → false
        check_env(parse("and false true", &env)?, T![false], &env);
        // and false false → false
        check_env(parse("and false false", &env)?, T![false], &env);

        // λb. b false true
        let not = parse("λb:Bool. if b then false else true", &env)?;
        env.insert_variable("not", not.clone(), type_of(&not, &env)?);

        // not true → false
        check_env(parse("not true", &env)?, T![false], &env);
        // not false → true
        check_env(parse("not false", &env)?, T![true], &env);

        // λb.λc. b true c
        let or = parse("λb:Bool.λc:Bool.if b then true else c", &env)?;
        env.insert_variable("or", or.clone(), type_of(&or, &env)?);

        // or true true → true
        check_env(parse("or true true", &env)?, T![true], &env);
        // or true false → true
        check_env(parse("or true false", &env)?, T![true], &env);
        // or false true → true
        check_env(parse("or false true", &env)?, T![true], &env);
        // or false false → false
        check_env(parse("or false false", &env)?, T![false], &env);
        Ok(())
    }

    #[test]
    fn test_shifting() -> Result<()> {
        let mut env = Env::new();
        let tru = parse("λt:Bool.λf:Bool.t", &env)?;
        env.insert_variable("tru", tru.clone(), type_of(&tru, &env)?);

        let id = parse("λx:Bool.x", &env)?;
        env.insert_variable("id", id.clone(), type_of(&id, &env)?);

        let id_shifted = shift(&id, 1)?;
        // Shouldn't touch id
        assert_eq!(id_shifted, id);

        let r#const = parse("λx:Bool.tru", &env)?;
        let const_shifted = shift(&r#const, 1)?;
        // Should shift true from 1 → 2
        assert_eq!(const_shifted, T![abs "x", TY![bool], T![var 2]]);

        let test = parse("tru id", &env)?;
        let test_shifted = shift_above(&test, 3, 1)?;
        assert_eq!(test_shifted, T![app T![var 0], T![var 4]]);
        assert_eq!(test, T![app T![var 0], T![var 1]]);

        // ↑²(λ.λ.1 (0 2))
        let book_example_1 = parse("λx:Bool.λy:Bool.x (y tru)", &env)?;
        let b_ex_1_shifted = shift(&book_example_1, 2)?;
        // Expected λ.λ.1 (0 4)
        assert_eq!(
            b_ex_1_shifted,
            T![abs "x", TY![bool], T![abs "y", TY![bool], T![app T![var 1], T![app T![var 0], T![var 4]]]]]
        );

        // ↑²(λ.0 1 (λ. 0 1 2))
        let book_example_2 = parse("λx:Bool.x tru (λy:Bool.y x tru)", &env)?;
        let b_ex_2_shifted = shift(&book_example_2, 2)?;
        // Expected λ.0 3 (λ. 0 1 4)
        assert_eq!(
            b_ex_2_shifted,
            T![abs "x", TY![bool], T![app T![app T![var 0], T![var 3]], T![abs "y", TY![bool], T![app T![app T![var 0], T![var 1]], T![var 4]]]]]
        );
        Ok(())
    }

    #[test]
    fn test_de_bruijn_indices_work() -> Result<()> {
        let mut env = Env::new();
        let t = parse("λt:Bool.λf:Bool.t", &env)?;
        assert_eq!(term_to_string(&t, &env)?, "λt:Bool.λf:Bool.t");

        let t = parse("λx:Bool.x x", &env)?;
        assert_eq!(term_to_string(&t, &env)?, "λx:Bool.x x");

        let t = parse("λx:Bool.λx:Bool.x", &env)?;
        assert_eq!(term_to_string(&t, &env)?, "λx:Bool.λx':Bool.x'");

        let t = parse("(λx:Bool → Bool.λy:Bool.x y) λx:Bool.x", &env)?;
        let t = eval(&t, &env)?;
        assert_eq!(term_to_string(&t, &env)?, "λy:Bool.(λx:Bool.x) y");

        let id = parse("λx:Bool.x", &env)?;
        env.insert_variable("id", id.clone(), type_of(&id, &env)?);

        let t = parse(
            "(λz:Bool → Bool.λid:(Bool → Bool) → Bool.id z) λz:Bool.id z",
            &env,
        )?;
        let t = eval(&t, &env)?;
        assert_eq!(
            term_to_string(&t, &env)?,
            "λid':(Bool → Bool) → Bool.id' λz:Bool.id z"
        );
        Ok(())
    }

    #[test]
    fn test_eval_nat() {
        check_parse("0", T![0]);
        check_parse("1", T![succ T![0]]);
        check_parse("iszero 0", T![true]);
        check_parse("iszero succ 0", T![false]);
        check_parse("iszero pred succ 0", T![true]);
        check_parse("pred 0", T![0]);
        check_parse("pred succ 0", T![0]);
        check_parse("pred pred pred pred 0", T![0]);
        check_parse("succ succ pred 0", T![succ T![succ T![0]]]);

        check_parse("pred 3", T![succ T![succ T![0]]]);
        check_parse("(λx:Nat.iszero pred x) 0", T![true]);
        check_parse("(λx:Nat.iszero pred x) 1", T![true]);
        check_parse("(λx:Nat.iszero pred x) 2", T![false]);
    }

    #[test]
    fn test_eval_unit() {
        check_parse("unit", T![unit]);
        check_parse("(λx:Nat.unit)3", T![unit]);
        check_parse("(λx:Unit.true)unit", T![true]);
    }
}
