use crate::types::LTy;
use crate::Error;
use crate::ErrorKind;
use crate::Span;
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
use std::rc::Rc;
use std::{collections::HashMap, convert::TryFrom};

type Result<T> = std::result::Result<T, Error>;

macro_rules! error {
    ($msg:expr; $span:expr) => {
        error!($msg,; $span)
    };
    ($msg:expr, $($arg:expr),*; $span:expr) => {
        Error::new(format!($msg, $($arg),*), $span, ErrorKind::Runtime)
    };
}

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
///     t as T              ascription
///     let x = t in t      let binding
/// ```
#[derive(Debug, Eq)]
pub struct Term {
    pub span: Span,
    pub kind: TermKind,
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermKind {
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
    Ascription(LTerm, LTy),
    Let(Symbol, LTerm, LTerm),
    Record(HashMap<Symbol, LTerm>, /** Original order of the keys */ Vec<Symbol>),
    Projection(LTerm, Symbol),
}

pub type LTerm = Rc<Term>;

pub fn eval(t: &LTerm, env: &Env) -> Result<LTerm> {
    type_of(&t, &env)?;
    eval_(&t, env)
}

// See NOTES.md for the evaluation rules
fn eval_(eval_t: &LTerm, env: &Env) -> Result<LTerm> {
    match eval_t.as_ref().kind {
        TermKind::Application(ref t1, ref t2) => {
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
            match v1.as_ref().kind {
                // E-AppAbs
                // (λ.t12)v2 → ↑⁻¹([0 → ↑¹(v2)]t12)
                TermKind::Abstraction(_, _, ref body) => eval_(&term_subst_top(&v2, &body)?, &env),
                _ => Err(error!(
                    "Expected an abstraction, got {}",
                    term_to_string(t1, &env)?;
                    v1.span
                )),
            }
        }
        TermKind::Variable(idx) => env
            .get_from_db_index(idx)
            .ok_or_else(|| error!("Invalid de Bruijn index: {}", idx; eval_t.span)),
        // Evaluating an abstraction, yields the abstraction itself.
        TermKind::If(ref cond, ref then, ref else_b) => {
            let cond = eval_(cond, &env)?;

            match cond.as_ref().kind {
                TermKind::True => eval_(then, &env),
                TermKind::False => eval_(else_b, &env),
                _ => Err(error!(
                    "Expected a boolean, got `{}`",
                    term_to_string(&cond, &env)?;
                    cond.span
                )),
            }
        }
        TermKind::Abstraction(_, _, _)
        | TermKind::True
        | TermKind::False
        | TermKind::Zero
        | TermKind::Unit => Ok(eval_t.clone()),
        TermKind::Succ(ref t) => {
            let t = eval_(t, &env)?;
            Ok(T![succ t; eval_t.span])
        }
        TermKind::Pred(ref t) => {
            let t = eval_(t, &env)?;
            match t.as_ref().kind {
                TermKind::Zero => Ok(T![0; eval_t.span]),
                TermKind::Succ(ref t) => Ok(t.clone()),
                _ => Err(error!(
                    "Expected a numeric value, got `{}`",
                    term_to_string(&t, &env)?;
                    t.span
                )),
            }
        }
        TermKind::IsZero(ref t) => {
            let t = eval_(t, &env)?;
            match t.as_ref().kind {
                TermKind::Zero => Ok(T![true; eval_t.span]),
                TermKind::Succ(_) => Ok(T![false; eval_t.span]),
                _ => Err(error!(
                    "Expected a numeric value, got `{}`",
                    term_to_string(&t, &env)?;
                    t.span
                )),
            }
        }
        // Type checking is done by type_of
        TermKind::Ascription(ref t, _) => eval_(t, env),
        TermKind::Let(x, ref t1, ref t2) => {
            let t1 = eval_(t1, &env)?;
            let mut env = Env::with_parent(&env);
            env.insert_let_term(x, t1.clone());
            eval_(&term_subst_top(&t1, &t2)?, &env)
        }
        TermKind::Record(ref elems, ref keys) => keys
            .iter()
            .cloned()
            .map(|k| eval_(elems.get(&k).unwrap(), &env).map(|e| (k, e)))
            .collect::<Result<HashMap<_, _>>>()
            .map(|elems| {
                Rc::new(Term {
                    kind: TermKind::Record(elems, keys.clone()),
                    span: eval_t.span,
                })
            }),
        TermKind::Projection(ref t, i) => {
            let t = eval_(t, &env)?;
            if i.as_str() == "0" {
                return Err(error!(
                    "Cannot access a record with `0`, projections start from `1`"; eval_t.span
                ));
            }
            match t.as_ref().kind {
                TermKind::Record(ref elems, _) => match elems.get(&i) {
                    Some(e) => Ok(e.clone()),
                    None => Err(error!("Couldn't get element `{}` from record", i; eval_t.span)),
                },
                _ => Err(error!("Projections can only be done over records"; eval_t.span)),
            }
        }
    }
}

// (λ.t₁₂)v₂ → ↑⁻¹([0 → ↑¹(v₂)]t₁₂)
fn term_subst_top(v2: &LTerm, t12: &LTerm) -> Result<LTerm> {
    shift(&substitute(t12, 0, &shift(v2, 1)?)?, -1)
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
fn substitute(t: &LTerm, db_idx: usize, arg: &LTerm) -> Result<LTerm> {
    term_map(t, 0, |idx, c| {
        if idx == c + db_idx {
            shift(
                &arg,
                isize::try_from(c).map_err(|_| error!("Too many bindings"; t.span))?,
            )
        } else {
            Ok(T![var idx; t.span])
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
            let idx =
                isize::try_from(idx).map_err(|_| error!("Too many bindings"; t.span))? + d_place;
            let new_idx = usize::try_from(idx)
                .map_err(|_| error!("Invalid negative de Bruijn index calculated"; t.span))?;
            T![var new_idx; t.span]
        } else {
            T![var idx; t.span]
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
        match t.as_ref().kind {
            TermKind::Variable(idx) => on_var(idx, cutoff),
            TermKind::Abstraction(v, ref ty, ref body) => {
                Ok(T![abs(v), ty, map(body, cutoff + 1, on_var)?; t.span])
            }
            TermKind::Application(ref t1, ref t2) => {
                Ok(T![app map(t1, cutoff, on_var)?, map(t2, cutoff, on_var)?; t.span])
            }
            TermKind::True | TermKind::False | TermKind::Zero | TermKind::Unit => Ok(t.clone()),
            TermKind::Succ(ref t) => Ok(T![succ map(t, cutoff, on_var)?; t.span]),
            TermKind::Pred(ref t) => Ok(T![pred map(t, cutoff, on_var)?; t.span]),
            TermKind::IsZero(ref t) => Ok(T![iszero map(t, cutoff, on_var)?; t.span]),
            TermKind::Ascription(ref t, _) => Ok(T![iszero map(t, cutoff, on_var)?; t.span]),
            TermKind::Record(ref elems, ref keys) => keys
                .iter()
                .cloned()
                .map(|k| map(elems.get(&k).unwrap(), cutoff, on_var).map(|e| (k, e)))
                .collect::<Result<HashMap<_, _>>>()
                .map(|elems| {
                    Rc::new(Term {
                        kind: TermKind::Record(elems, keys.clone()),
                        span: t.span,
                    })
                }),
            TermKind::Let(x, ref t1, ref t2) => {
                Ok(T![let x, map(t1, cutoff, on_var)?, map(t2, cutoff + 1, on_var)?; t.span])
            }
            TermKind::If(ref cond, ref then, ref else_b) => Ok(T![if
                                               map(cond, cutoff, on_var)?,
                                               map(then, cutoff, on_var)?,
                                               map(else_b, cutoff, on_var)?;
            t.span]),
            TermKind::Projection(ref t, i) => Ok(T![proj map(t, cutoff, on_var)?, i; t.span]),
        }
    }
    map(t, cutoff, &on_var)
}

pub fn term_to_string(t: &LTerm, env: &Env) -> Result<String> {
    fn symbol_to_record_key(s: Symbol) -> String {
        if s.as_str().parse::<u64>().is_ok() {
            String::new()
        } else {
            format!("{}=", s)
        }
    }

    match t.as_ref().kind {
        TermKind::Variable(idx) => match env.get_name_from_db_index(idx) {
            Some(v) => Ok(v.to_string()),
            None => Err(error!("Invalid de Bruijn index: {}", idx; t.span)),
        },
        TermKind::Abstraction(param, ref ty, ref body) => {
            let (param, env) = new_name(param, ty, &env);
            Ok(format!("λ{}:{}.{}", param, ty, term_to_string(body, &env)?))
        }
        TermKind::Application(ref t1, ref t2) => {
            let t1_paren = matches!(t1.kind, TermKind::Abstraction(_, _, _));
            let t2_paren = matches!(t2.kind, TermKind::Application(_, _));
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
        TermKind::Unit => Ok(String::from("unit")),
        TermKind::True => Ok(String::from("true")),
        TermKind::False => Ok(String::from("false")),
        TermKind::Zero => Ok(String::from("0")),
        TermKind::Pred(ref t) => Ok(format!("pred {}", term_to_string(t, &env)?)),
        TermKind::Succ(ref t) => Ok(format!("succ {}", term_to_string(t, &env)?)),
        TermKind::IsZero(ref t) => Ok(format!("iszero {}", term_to_string(t, &env)?)),
        TermKind::Ascription(ref t, _) => term_to_string(t, &env),
        TermKind::If(ref c, ref t, ref e) => Ok(format!(
            "if {} then {} else {}",
            term_to_string(c, &env)?,
            term_to_string(t, &env)?,
            term_to_string(e, &env)?,
        )),
        TermKind::Let(x, ref t1, ref t2) => Ok(format!(
            "let {} = {} in {}",
            x,
            term_to_string(t1, &env)?,
            term_to_string(t2, &env)?,
        )),
        TermKind::Record(ref elems, ref keys) => {
            Ok(format!(
                "{{{}}}",
                keys.iter()
                    .cloned()
                    .map(
                        |k| term_to_string(elems.get(&k).unwrap(), &env).map(|e| format!(
                            "{}{}",
                            symbol_to_record_key(k),
                            e
                        ))
                    )
                    .collect::<Result<Vec<_>>>()?
                    .join(", ")
            ))
        }
        TermKind::Projection(ref t, i) => Ok(format!("{}.{}", term_to_string(t, &env)?, i,)),
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
    (var $n:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Variable($n), span: $span.into() })
    };
    (abs $param:expr, $ty:expr, $body:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Abstraction($param.into(), $ty.clone(), $body.clone()), span: $span.into() })
    };
    (app $t1:expr, $t2:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Application($t1.clone(), $t2.clone()), span: $span.into() })
    };
    (asc $t:expr, $ty:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Ascription($t.clone(), $ty.clone()), span: $span.into() })
    };
    (true; $span:expr) => {
        Rc::new(Term { kind: TermKind::True, span: $span.into() })
    };
    (false; $span:expr) => {
        Rc::new(Term { kind: TermKind::False, span: $span.into() })
    };
    (if $cond:expr, $then:expr, $else:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::If($cond.clone(), $then.clone(), $else.clone()), span: $span.into() })
    };
    (0; $span:expr) => {
        Rc::new(Term { kind: TermKind::Zero, span: $span.into() })
    };
    (succ $t:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Succ($t.clone()), span: $span.into() })
    };
    (pred $t:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Pred($t.clone()), span: $span.into() })
    };
    (iszero $t:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::IsZero($t.clone()), span: $span.into() })
    };
    (unit; $span:expr) => {
        Rc::new(Term { kind: TermKind::Unit, span: $span.into() })
    };
    (let $var:expr, $expr:expr, $body:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Let($var.into(), $expr.clone(), $body.clone()), span: $span.into() })
    };
    (record $($term:expr),*; $span:expr) => {
        Rc::new(Term { kind: TermKind::Record(vec![$($term.clone()),*]), span: $span.into() })
    };
    (proj $term:expr, $elem:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Projection($term.clone(), $elem), span: $span.into() })
    };
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use super::*;
    use crate::{parser::parse, types::type_of, TY};
    use crate::{types::Ty, types::TyKind};
    use std::rc::Rc;

    const SPAN: Span = Span::new(0, 1);

    fn check(input: &str, expected: expect_test::Expect) {
        let env = Env::new();
        expected.assert_eq(
            &term_to_string(
                &eval(&parse(input, &env).expect("Couldn't parse"), &env)
                    .expect("Couldn't evaluate"),
                &Env::new(),
            )
            .expect("Couldn't stringify"),
        );
    }

    fn new_check_env(input: &str, expected: expect_test::Expect, env: &Env) {
        expected.assert_eq(
            &term_to_string(
                &eval(&parse(input, &env).expect("Couldn't parse"), &env)
                    .expect("Couldn't evaluate"),
                &env,
            )
            .expect("Couldn't stringify"),
        );
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
    fn test_eval_abstraction() {
        check("λx:Bool.x", expect![["λx:Bool.x"]]);
    }

    #[test]
    fn test_application_abstraction_to_abstraction() -> Result<()> {
        let mut env = Env::new();
        let id = parse("λx:Bool.x", &env)?;
        let apply_fn = parse("λf:Bool → Bool.λb:Bool.f b", &env)?;
        env.insert_variable("id", id.clone(), type_of(&id, &env)?);
        env.insert_variable("applyfn", apply_fn.clone(), type_of(&apply_fn, &env)?);
        new_check_env("applyfn id", expect![["λb:Bool.(λx:Bool.x) b"]], &env);

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

        new_check_env("and true true", expect![["true"]], &env);
        new_check_env("and true false", expect![["false"]], &env);
        new_check_env("and false true", expect![["false"]], &env);
        new_check_env("and false false", expect![["false"]], &env);

        // λb. b false true
        let not = parse("λb:Bool. if b then false else true", &env)?;
        env.insert_variable("not", not.clone(), type_of(&not, &env)?);

        new_check_env("not true", expect![["false"]], &env);
        new_check_env("not false", expect![["true"]], &env);

        // λb.λc. b true c
        let or = parse("λb:Bool.λc:Bool.if b then true else c", &env)?;
        env.insert_variable("or", or.clone(), type_of(&or, &env)?);

        new_check_env("or true true", expect![["true"]], &env);
        new_check_env("or true false", expect![["true"]], &env);
        new_check_env("or false true", expect![["true"]], &env);
        new_check_env("or false false", expect![["false"]], &env);

        let eq = parse("λb1:Bool.λb2:Bool.if b1 then b2 else not b2", &env)?;
        env.insert_variable("eq", eq.clone(), type_of(&eq, &env)?);
        new_check_env("eq true true", expect![["true"]], &env);
        new_check_env("eq false true", expect![["false"]], &env);
        new_check_env("eq true false", expect![["false"]], &env);
        new_check_env("eq false false", expect![["true"]], &env);

        let eq = parse("λb1:Bool.λb2:Bool.not (eq b1 b2)", &env)?;
        env.insert_variable("neq", eq.clone(), type_of(&eq, &env)?);
        new_check_env("neq true true", expect![["false"]], &env);
        new_check_env("neq false true", expect![["true"]], &env);
        new_check_env("neq true false", expect![["true"]], &env);
        new_check_env("neq false false", expect![["false"]], &env);

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
        assert_eq!(
            const_shifted,
            T![abs "x", TY![bool; SPAN], T![var 2; SPAN]; SPAN]
        );

        let test = parse("tru id", &env)?;
        let test_shifted = shift_above(&test, 3, 1)?;
        assert_eq!(test_shifted, T![app T![var 0; SPAN], T![var 4; SPAN]; SPAN]);
        assert_eq!(test, T![app T![var 0; SPAN], T![var 1; SPAN]; SPAN]);

        // ↑²(λ.λ.1 (0 2))
        let book_example_1 = parse("λx:Bool.λy:Bool.x (y tru)", &env)?;
        let b_ex_1_shifted = shift(&book_example_1, 2)?;
        // Expected λ.λ.1 (0 4)
        assert_eq!(
            b_ex_1_shifted,
            T![abs "x", TY![bool; SPAN], T![abs "y", TY![bool; SPAN], T![app T![var 1; SPAN], T![app T![var 0; SPAN], T![var 4; SPAN]; SPAN]; SPAN]; SPAN]; SPAN]
        );

        // ↑²(λ.0 1 (λ. 0 1 2))
        let book_example_2 = parse("λx:Bool.x tru (λy:Bool.y x tru)", &env)?;
        let b_ex_2_shifted = shift(&book_example_2, 2)?;
        // Expected λ.0 3 (λ. 0 1 4)
        assert_eq!(
            b_ex_2_shifted,
            T![abs "x", TY![bool; SPAN], T![app T![app T![var 0; SPAN], T![var 3; SPAN]; SPAN], T![abs "y", TY![bool; SPAN], T![app T![app T![var 0; SPAN], T![var 1; SPAN]; SPAN], T![var 4; SPAN]; SPAN]; SPAN]; SPAN]; SPAN]
        );
        Ok(())
    }

    #[test]
    fn test_de_bruijn_indices() -> Result<()> {
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
        check("0", expect![["0"]]);
        check("1", expect![["succ 0"]]);
        check("iszero 0", expect![[r#"true"#]]);
        check("iszero succ 0", expect![[r#"false"#]]);
        check("iszero pred succ 0", expect![[r#"true"#]]);
        check("pred 0", expect![[r#"0"#]]);
        check("pred succ 0", expect![[r#"0"#]]);
        check("pred pred pred pred 0", expect![[r#"0"#]]);
        check("succ succ pred 0", expect![[r#"succ succ 0"#]]);
        check("pred 3", expect![[r#"succ succ 0"#]]);
        check("(λx:Nat.iszero pred x) 0", expect![[r#"true"#]]);
        check("(λx:Nat.iszero pred x) 1", expect![[r#"true"#]]);
        check("(λx:Nat.iszero pred x) 2", expect![[r#"false"#]]);
    }

    #[test]
    fn test_eval_unit() {
        check("unit", expect![[r#"unit"#]]);
        check("(λx:Nat.unit)3", expect![[r#"unit"#]]);
        check("(λx:Unit.true)unit", expect![[r#"true"#]]);
    }

    #[test]
    fn test_eval_ascription() {
        check("true as Bool", expect![[r#"true"#]]);
        check("0 as Nat", expect![[r#"0"#]]);
        check("(λx:Bool.x) as Bool → Bool", expect![[r#"λx:Bool.x"#]]);
    }

    #[test]
    fn test_eval_let_binding() {
        check("let x = true in true", expect![[r#"true"#]]);
        check(
            "(let not = λb:Bool.if b then false else true in not) true",
            expect![[r#"false"#]],
        );
        check(
            r#"let not = λb:Bool.if b then false else true
                   in let and = λb1:Bool.λb2:Bool.if b1 then b2 else false
                      in and (not false) (not false)"#,
            expect![[r#"true"#]],
        );
        check(
            r#"let not = λb:Bool.if b then false else true
                   in let and = λb1:Bool.λb2:Bool.if b1 then b2 else false
                      in let nand = λb1:Bool.λb2:Bool.not (and b1 b2)
                         in nand false false"#,
            expect![[r#"true"#]],
        );
    }

    #[test]
    fn test_eval_record() {
        check("{true, true}", expect![[r#"{true, true}"#]]);
        check(
            "{first=true, last=true}",
            expect![[r#"{first=true, last=true}"#]],
        );
        check("{first=true, last=false}.first", expect![[r#"true"#]]);
        check("{first=true, last=false}.last", expect![[r#"false"#]]);
        check("{first=true, 0, last=false}.2", expect![[r#"0"#]]);
        check(
            "{(λb:Bool.b) true, (λb:Bool.b) true}",
            expect![[r#"{true, true}"#]],
        );
        check("{true}.1", expect![[r#"true"#]]);
        check("(λt:{Bool,Bool}.t.1) {false, true}", expect![[r#"false"#]]);
    }
}
