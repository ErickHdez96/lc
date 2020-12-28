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
/// The leftmost, outermost redex is always reduced first.
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
use crate::{
    env::{Env, TyEnv},
    types::type_of,
};
use std::{cell::RefCell, collections::HashMap, convert::TryFrom};
use std::{fmt, rc::Rc};

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
    /// true
    True,
    /// false
    False,
    /// if t₁ then ₂ else t₃
    If(LTerm, LTerm, LTerm),
    /// 0
    Zero,
    /// succ t
    Succ(LTerm),
    /// pred t
    Pred(LTerm),
    /// iszero t
    IsZero(LTerm),
    /// unit
    Unit,
    /// t as T
    Ascription(LTerm, LTy),
    /// let x = t₁ in t₂
    Let(Box<Pattern>, LTerm, LTerm),
    /// {lᵢ=tᵢ}
    Record(
        HashMap<Symbol, LTerm>,
        /** Original order of the keys */ Vec<Symbol>,
    ),
    /// t.l (label)
    Projection(LTerm, Symbol),
    /// let x = t;
    VariableDefinition(Box<Pattern>, LTerm),
    /// type x = T;
    TypeDefinition(Symbol, LTy),
    /// <l=t> as T
    Variant(Symbol, LTerm),
    /// case t of <lᵢ:xᵢ> ⇒ tᵢ (i∈1..n)
    Case(
        LTerm,
        CaseBranches,
        /* For printing purposes */ Vec<Symbol>,
    ),
    Fix(LTerm),
    Nil(LTy),
    Cons(LTerm, LTerm, LTy),
    IsNil(LTerm, LTy),
    Head(LTerm, LTy),
    Tail(LTerm, LTy),
    Ref(LTerm),
    Deref(LTerm),
    RefAssign(LTerm, LTerm),
    Location(RefCell<LTerm>),
}

pub type CaseBranches = HashMap<Symbol, (Symbol, LTerm)>;

pub type LTerm = Rc<Term>;

impl Term {
    pub fn is_definition(&self) -> bool {
        match &self.kind {
            TermKind::Application(_, ref t2) => t2.is_definition(),
            TermKind::VariableDefinition(_, _) | TermKind::TypeDefinition(_, _) => true,
            _ => false,
        }
    }
}

// TODO: Improve clones, probably with Rc
// TODO: Save spans for better errors
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Var(Symbol),
    Record(HashMap<Symbol, Box<Pattern>>, Vec<Symbol>),
}

pub fn eval(t: &LTerm, env: &mut Env, tyenv: &mut TyEnv) -> Result<LTerm> {
    type_of(&t, env, tyenv)?;
    eval_(&t, env)
}

// See NOTES.md for the evaluation rules
fn eval_(eval_t: &LTerm, env: &mut Env) -> Result<LTerm> {
    match eval_t.kind {
        TermKind::Application(ref t1, ref t2) => {
            // If t1 is `let x = t;` or `type A = T;`, we can ignore the result
            // of evaluating it (i.e. unit) and just return `t2`.
            let ignore_t1 = t1.is_definition();
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
            match v1.kind {
                // E-AppAbs
                // (λ.t12)v2 → ↑⁻¹([0 → ↑¹(v2)]t12)
                TermKind::Abstraction(_, _, ref body) => eval_(&term_subst_top(&v2, &body)?, env),
                _ if ignore_t1 => Ok(v2),
                _ => Err(error!(
                    "Expected an abstraction, got {}",
                    term_to_string(t1, &env)?;
                    v1.span
                )),
            }
        }
        TermKind::Variable(idx) => env
            .get_term_from_index(idx)
            .ok_or_else(|| error!("Invalid de Bruijn index: {}", idx; eval_t.span)),
        // Evaluating an abstraction, yields the abstraction itself.
        TermKind::If(ref cond, ref then, ref else_b) => {
            let cond = eval_(cond, env)?;

            match cond.kind {
                TermKind::True => eval_(then, env),
                TermKind::False => eval_(else_b, env),
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
        | TermKind::Unit
        | TermKind::Nil(_)
        | TermKind::Location(_) => Ok(Rc::clone(eval_t)),
        TermKind::Succ(ref t) => {
            let t = eval_(t, env)?;
            Ok(T![succ t; eval_t.span])
        }
        TermKind::Pred(ref t) => {
            let t = eval_(t, env)?;
            match t.kind {
                TermKind::Zero => Ok(T![0; eval_t.span]),
                TermKind::Succ(ref t) => Ok(Rc::clone(t)),
                _ => Err(error!(
                    "Expected a numeric value, got `{}`",
                    term_to_string(&t, &env)?;
                    t.span
                )),
            }
        }
        TermKind::IsZero(ref t) => {
            let t = eval_(t, env)?;
            match t.kind {
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
        TermKind::Let(ref p, ref t1, ref t2) => {
            let t1 = eval_(t1, env)?;
            eval_(&term_subst_top_pattern(&t1, p, t2)?, env)
        }
        TermKind::Record(ref elems, ref keys) => keys
            .iter()
            .cloned()
            .map(|k| eval_(elems.get(&k).unwrap(), env).map(|e| (k, e)))
            .collect::<Result<HashMap<_, _>>>()
            .map(|elems| {
                Rc::new(Term {
                    kind: TermKind::Record(elems, keys.clone()),
                    span: eval_t.span,
                })
            }),
        TermKind::Projection(ref t, i) => {
            let t = eval_(t, env)?;
            if i.as_str() == "0" {
                return Err(error!(
                    "Cannot access a record with `0`, projections start from `1`"; eval_t.span
                ));
            }
            let tb = t;
            match tb.kind {
                TermKind::Record(ref elems, _) => match elems.get(&i) {
                    Some(e) => Ok(Rc::clone(e)),
                    None => Err(error!("Couldn't get element `{}` from record", i; eval_t.span)),
                },
                _ => Err(error!("Projections can only be done over records"; eval_t.span)),
            }
        }
        TermKind::VariableDefinition(ref p, ref t) => {
            let t = eval_(t, env)?;
            resolve_match_mut(p, &t, env)?;
            Ok(T![unit; eval_t.span])
        }
        TermKind::TypeDefinition(_, _) => Ok(T![unit; eval_t.span]),
        TermKind::Variant(label, ref term) => {
            let term = eval_(term, env)?;
            Ok(T![variant label, term; eval_t.span])
        }
        TermKind::Case(ref term, ref branches, _) => {
            let term = eval_(term, env)?;
            let (variant, term) = if let TermKind::Variant(label, ref t) = term.kind {
                (label, t)
            } else {
                return Err(
                    error!("There was an error during type checking, expected a variant"; term.span),
                );
            };

            match branches.get(&variant) {
                Some((_, body)) => eval_(&term_subst_top(term, body)?, env),
                None => match branches.get(&Symbol::from("_")) {
                    Some((_, body)) => eval_(&term_subst_top(term, body)?, env),
                    None => Err(
                        error!("There was an error during type checking, invalid label"; term.span),
                    ),
                },
            }
        }
        TermKind::Fix(ref t) => {
            let t = eval_(t, env)?;

            match t.kind {
                TermKind::Abstraction(_, _, ref t2) => {
                    let t = Rc::new(Term {
                        span: eval_t.span,
                        kind: TermKind::Fix(Rc::clone(&t)),
                    });
                    eval_(&term_subst_top(&t, t2)?, env)
                }
                _ => Err(
                    error!("Fix expects an abstraction, got `{}`", term_to_string(&t, env)?; eval_t.span),
                ),
            }
        }
        TermKind::Cons(ref t1, ref t2, ref ty) => {
            let v1 = eval_(t1, env)?;
            let v2 = eval_(t2, env)?;
            Ok(Rc::new(Term {
                span: eval_t.span,
                kind: TermKind::Cons(v1, v2, Rc::clone(ty)),
            }))
        }
        TermKind::IsNil(ref t, _) => {
            let v = eval_(t, env)?;
            Ok(Rc::new(Term {
                span: eval_t.span,
                kind: if matches!(v.kind, TermKind::Nil(_)) {
                    TermKind::True
                } else {
                    TermKind::False
                },
            }))
        }
        TermKind::Head(ref t, _) => {
            let v = eval_(t, env)?;

            match v.kind {
                TermKind::Cons(ref h, _, _) => Ok(Rc::clone(h)),
                _ => Err(error!("Tried to get the head of an empty list"; eval_t.span)),
            }
        }
        TermKind::Tail(ref t, _) => {
            let v = eval_(t, env)?;
            match v.kind {
                TermKind::Cons(_, ref t, _) => Ok(Rc::clone(t)),
                _ => Err(error!("Tried to get the tail of an empty list"; eval_t.span)),
            }
        }
        TermKind::Ref(ref t) => {
            let t = eval_(t, env)?;
            Ok(Rc::new(Term {
                span: eval_t.span,
                kind: TermKind::Location(RefCell::new(t)),
            }))
        }
        TermKind::Deref(ref t) => {
            let t = eval_(t, env)?;
            match t.kind {
                TermKind::Location(ref t) => Ok(Rc::clone(&t.borrow())),
                _ => Err(error!("Cannot dereference `{}`", term_to_string(&t, env)?; eval_t.span)),
            }
        }
        TermKind::RefAssign(ref t1, ref t2) => {
            let t1 = eval_(t1, env)?;
            let t2 = eval_(t2, env)?;

            match t1.kind {
                TermKind::Location(ref t) => {
                    *t.borrow_mut() = t2;
                    Ok(T![unit; eval_t.span])
                }
                _ => Err(error!("Cannot assign to `{}`", term_to_string(&t1, env)?; eval_t.span)),
            }
        }
    }
}

/// We iterate over the pattern substituting from left to right.
///
/// ```text
/// let x = true in (x db:0)
/// > [x → true](x db:0)
/// > true
///
/// let {x, y} = {true, false} in {(x db:0), (y db:1)}
/// > [x → true]{(x db:0), (y db:1)}
/// > [y → false]{true, (y db:0)}
/// > {true, false}
///
/// let {{x, y}, {z, a}} = {{true, false}, {0, unit}} in {{(a db:3), (z db:2)}, {(y db:1), (x db:0)}}
/// > [x → true]{{(a db:3), (z db:2)}, {(y db:1), (x db:0)}}
/// > [y → false]{{(a db:3), (z db:2)}, {(y db:1), true}}
/// > [z → 0]{{(a db:3), (z db:2)}, {false, true}}
/// > [a → unit]{{(a db:3), 0}, {false, true}}
/// > {{unit, 0}, {false, true}}
/// ```
fn term_subst_top_pattern(v2: &LTerm, p: &Pattern, t12: &LTerm) -> Result<LTerm> {
    match p {
        Pattern::Var(_) => {
            // Once we reach a variable, we know it is the leftmost one.
            // Since `let x = t1 in t2` is similar to (λx.t2)t1
            // We know that any reference to `x` has the de Bruijn index 0.
            // So we substitute the current variable with the current term.
            shift(&substitute(t12, 0, &shift(&v2, 1)?)?, -1)
        }
        Pattern::Record(recs, keys) => match v2.kind {
            // If we find a record, we iterate over the keys from left to right,
            // in the order they were introduced to the environment.
            // The leftmost variable we can find will always have de Bruijn index 0.
            //
            // Record patterns are only allowed to match over records `let {x} = true in x` is
            // nonsensical.
            TermKind::Record(ref trecs, _) => {
                let mut t12 = Rc::clone(t12);

                for key in keys {
                    // We get the term pointed to by the current key and recursively call the
                    // substitution function, this allows us to match deeply nested record
                    // patterns.
                    //
                    // Note: for tuples (i.e. `{x, y}`), the keys we iterate over are the indices
                    // of their members (beginning at 1). The keys for the previous tuple would be
                    // [1, 2]. Then we would pattern match against to variables, `x`, and `y`.
                    match trecs.get(key) {
                        Some(v2) => {
                            t12 = term_subst_top_pattern(v2, recs.get(key).unwrap(), &t12)?;
                        }
                        None => {
                            return Err(
                                error!("The key `{}` does not exist in the record", key; t12.span),
                            );
                        }
                    }
                }

                Ok(t12)
            }
            _ => Err(error!("Only records can be pattern matched"; t12.span)),
        },
    }
}

fn resolve_match<'a>(p: &Pattern, t: &LTerm, env: &'a Env) -> Result<Env<'a>> {
    let mut env = Env::with_parent(&env);
    resolve_match_mut(p, t, &mut env)?;
    Ok(env)
}

fn resolve_match_mut(p: &Pattern, t: &LTerm, mut env: &mut Env) -> Result<()> {
    match p {
        Pattern::Var(s) => {
            env.insert_term(*s, t)?;
            Ok(())
        }
        Pattern::Record(recs, keys) => match t.kind {
            TermKind::Record(ref trecs, ref tkeys) => {
                for (i, key) in keys.iter().copied().enumerate() {
                    // The keys must be in the same order
                    match tkeys.get(i).copied() {
                        Some(k) if k == key => {
                            resolve_match_mut(
                                recs.get(&key).unwrap(),
                                trecs.get(&key).unwrap(),
                                &mut env,
                            )?;
                        }
                        Some(_) => {
                            return Err(
                                error!("Match keys must follow the same order as the record"; t.span),
                            );
                        }
                        None => {
                            return Err(
                                error!("The key `{}` does not exist in the record", key; t.span),
                            );
                        }
                    }
                }
                Ok(())
            }
            _ => Err(error!("Only records can be pattern matched"; t.span)),
        },
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
        match t.kind {
            TermKind::Variable(idx) => on_var(idx, cutoff),
            TermKind::Abstraction(v, ref ty, ref body) => {
                Ok(T![abs(v), ty, map(body, cutoff + 1, on_var)?; t.span])
            }
            TermKind::Application(ref t1, ref t2) => {
                Ok(T![app map(t1, cutoff, on_var)?, map(t2, cutoff, on_var)?; t.span])
            }
            TermKind::True
            | TermKind::False
            | TermKind::Zero
            | TermKind::Unit
            | TermKind::Nil(_) => Ok(Rc::clone(t)),
            TermKind::Succ(ref t) => Ok(T![succ map(t, cutoff, on_var)?; t.span]),
            TermKind::Pred(ref t) => Ok(T![pred map(t, cutoff, on_var)?; t.span]),
            TermKind::IsZero(ref t) => Ok(T![iszero map(t, cutoff, on_var)?; t.span]),
            TermKind::Ascription(ref t, ref ty) => Ok(T![asc map(t, cutoff, on_var)?, ty; t.span]),
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
            TermKind::Let(ref p, ref t1, ref t2) => Ok(
                T![let p.clone(), map(t1, cutoff, on_var)?, map(t2, cutoff + 1, on_var)?; t.span],
            ),
            TermKind::If(ref cond, ref then, ref else_b) => Ok(T![if
                                               map(cond, cutoff, on_var)?,
                                               map(then, cutoff, on_var)?,
                                               map(else_b, cutoff, on_var)?;
            t.span]),
            TermKind::Projection(ref t, i) => Ok(T![proj map(t, cutoff, on_var)?, i; t.span]),
            TermKind::VariableDefinition(_, _) => {
                Err(error!("A definition should not be mapped"; t.span))
            }
            TermKind::TypeDefinition(_, _) => {
                Err(error!("A definition should not be mapped"; t.span))
            }
            TermKind::Variant(label, ref term) => {
                Ok(T![variant label, map(term, cutoff, on_var)?; t.span])
            }
            TermKind::Case(ref case_t, ref branches, ref symbols) => {
                let case_t = map(case_t, cutoff, on_var)?;
                symbols
                    .iter()
                    .copied()
                    .map(|k| {
                        let (branch_var, branch_term) = branches.get(&k).unwrap();
                        map(branch_term, cutoff + 1, on_var).map(|t| (k, (*branch_var, t)))
                    })
                    .collect::<Result<HashMap<_, _>>>()
                    .map(|elems| {
                        Rc::new(Term {
                            span: t.span,
                            kind: TermKind::Case(case_t, elems, symbols.clone()),
                        })
                    })
            }
            TermKind::Fix(ref fft) => Ok(Rc::new(Term {
                span: t.span,
                kind: TermKind::Fix(map(fft, cutoff, on_var)?),
            })),
            TermKind::Cons(ref t1, ref t2, ref ty) => Ok(Rc::new(Term {
                span: t.span,
                kind: TermKind::Cons(
                    map(t1, cutoff, on_var)?,
                    map(t2, cutoff, on_var)?,
                    Rc::clone(ty),
                ),
            })),
            TermKind::IsNil(ref l, ref ty) => Ok(Rc::new(Term {
                span: t.span,
                kind: TermKind::IsNil(map(l, cutoff, on_var)?, Rc::clone(ty)),
            })),
            TermKind::Head(ref l, ref ty) => Ok(Rc::new(Term {
                span: t.span,
                kind: TermKind::Head(map(l, cutoff, on_var)?, Rc::clone(ty)),
            })),
            TermKind::Tail(ref l, ref ty) => Ok(Rc::new(Term {
                span: t.span,
                kind: TermKind::Tail(map(l, cutoff, on_var)?, Rc::clone(ty)),
            })),
            TermKind::Ref(ref td) => Ok(Rc::new(Term {
                span: t.span,
                kind: TermKind::Ref(map(td, cutoff, on_var)?),
            })),
            TermKind::Deref(ref td) => Ok(Rc::new(Term {
                span: t.span,
                kind: TermKind::Deref(map(td, cutoff, on_var)?),
            })),
            TermKind::RefAssign(ref t1, ref t2) => Ok(Rc::new(Term {
                span: t.span,
                kind: TermKind::RefAssign(map(t1, cutoff, on_var)?, map(t2, cutoff, on_var)?),
            })),
            TermKind::Location(ref td) => {
                let mapped = map(&td.borrow(), cutoff, on_var)?;
                *td.borrow_mut() = mapped;
                Ok(Rc::clone(t))
            }
        }
    }
    map(t, cutoff, &on_var)
}

pub fn term_to_string(t: &LTerm, env: &Env) -> Result<String> {
    match t.kind {
        TermKind::Variable(idx) => match env.get_name_from_db_index(idx) {
            Some(v) => Ok(v.to_string()),
            None => Err(error!("Invalid de Bruijn index: {}", idx; t.span)),
        },
        TermKind::Abstraction(param, ref ty, ref body) => {
            let (param, env) = new_name(param, &env);
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
        TermKind::Succ(ref t) => {
            let mut n = 1u64;
            let mut inner_t = Rc::clone(t);

            loop {
                let ib = inner_t.kind.clone();
                match ib {
                    TermKind::Succ(t) => {
                        n += 1;
                        inner_t = t;
                    }
                    TermKind::Zero => {
                        break;
                    }
                    _ => {
                        return Ok(format!("succ {}", term_to_string(t, &env)?));
                    }
                }
            }

            Ok(format!("{}", n))
        }
        TermKind::IsZero(ref t) => Ok(format!("iszero {}", term_to_string(t, &env)?)),
        TermKind::Ascription(ref t, _) => term_to_string(t, &env),
        TermKind::If(ref c, ref t, ref e) => Ok(format!(
            "if {} then {} else {}",
            term_to_string(c, &env)?,
            term_to_string(t, &env)?,
            term_to_string(e, &env)?,
        )),
        TermKind::Let(ref p, ref t1, ref t2) => {
            let env = resolve_match(p, t1, &env)?;
            Ok(format!(
                "let {} = {} in {}",
                p,
                term_to_string(t1, &env)?,
                term_to_string(t2, &env)?,
            ))
        }
        TermKind::Record(ref elems, ref keys) => Ok(format!(
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
        )),
        TermKind::Projection(ref t, i) => Ok(format!("{}.{}", term_to_string(t, &env)?, i,)),
        TermKind::VariableDefinition(ref p, ref t) => {
            let env = resolve_match(p, t, &env)?;
            Ok(format!("let {} = {};", p, term_to_string(t, &env)?,))
        }
        TermKind::TypeDefinition(ref v, ref ty) => Ok(format!("type {} = {};", v, ty)),
        TermKind::Variant(label, ref term) => {
            Ok(format!("<{}={}>", label, term_to_string(term, &env)?,))
        }
        TermKind::Case(ref case_v, ref branches, ref keys) => Ok(format!(
            "case {} of {}",
            term_to_string(case_v, &env)?,
            keys.iter()
                .copied()
                .map(|variant| {
                    let (x, term) = branches.get(&variant).unwrap();
                    let (x, env) = new_name(*x, &env);
                    let case_output = if variant.as_str() == "_" {
                        String::from("_")
                    } else {
                        format!("<{}={}>", variant, x)
                    };
                    Ok(format!("{} ⇒ {}", case_output, term_to_string(term, &env)?))
                })
                .collect::<Result<Vec<_>>>()?
                .join(" | "),
        )),
        TermKind::Fix(ref t) => Ok(format!("fix {}", term_to_string(t, &env)?,)),
        TermKind::Nil(ref ty) => Ok(format!("nil[{}]", ty)),
        TermKind::Cons(ref t1, ref t2, ref ty) => Ok(format!(
            "cons[{}] {} {}",
            ty,
            term_to_string(t1, &env)?,
            term_to_string(t2, &env)?,
        )),
        TermKind::IsNil(ref t, ref ty) => {
            Ok(format!("isnil[{}] {}", ty, term_to_string(t, &env)?,))
        }
        TermKind::Head(ref t, ref ty) => Ok(format!("head[{}] {}", ty, term_to_string(t, &env)?,)),
        TermKind::Tail(ref t, ref ty) => Ok(format!("tail[{}] {}", ty, term_to_string(t, &env)?,)),
        TermKind::Ref(ref t) => Ok(format!("ref {}", term_to_string(t, &env)?)),
        TermKind::Location(ref t) => Ok(format!("ref {}", term_to_string(&t.borrow(), &env)?)),
        TermKind::Deref(ref t) => Ok(format!("!{}", term_to_string(t, &env)?)),
        TermKind::RefAssign(ref t1, ref t2) => Ok(format!(
            "{} := {}",
            term_to_string(t1, &env)?,
            term_to_string(t2, &env)?
        )),
    }
}

fn new_name<'a>(s: impl Into<Symbol>, env: &'a Env) -> (Symbol, Env<'a>) {
    let mut current_symbol = s.into();
    while env.get_db_index(current_symbol).is_some() {
        current_symbol = Symbol::from(format!("{}'", current_symbol));
    }
    let mut new_env = Env::with_parent(&env);
    new_env
        .insert_symbol(current_symbol, Span::new(0, 1))
        .expect("Name should have been unique");
    (current_symbol, new_env)
}

fn symbol_to_record_key(s: Symbol) -> String {
    if s.as_str().parse::<u64>().is_ok() {
        String::new()
    } else {
        format!("{}=", s)
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::Var(x) => x.fmt(f),
            Pattern::Record(rec, vars) => write!(
                f,
                "{{{}}}",
                vars.iter()
                    .copied()
                    .map(|k| format!("{}{}", symbol_to_record_key(k), rec.get(&k).unwrap()))
                    .collect::<Vec<_>>()
                    .join(", "),
            ),
        }
    }
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
    (var $var:expr, $expr:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::VariableDefinition($var.into(), $expr.clone()), span: $span.into() })
    };
    (record $($term:expr),*; $span:expr) => {
        Rc::new(Term { kind: TermKind::Record(vec![$($term.clone()),*]), span: $span.into() })
    };
    (proj $term:expr, $elem:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Projection($term.clone(), $elem), span: $span.into() })
    };
    (variant $label:expr, $term:expr; $span:expr) => {
        Rc::new(Term { kind: TermKind::Variant($label.into(), $term.clone()), span: $span.into() })
    };
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use super::*;
    use crate::{env::base_env, parser::parse, types::type_of};

    fn check(input: &str, expected: expect_test::Expect) {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        expected.assert_eq(
            &term_to_string(
                &eval(
                    &parse(input, &mut env).expect("Couldn't parse"),
                    &mut env,
                    &mut tyenv,
                )
                .expect("Couldn't evaluate"),
                &Env::new(),
            )
            .expect("Couldn't stringify"),
        );
    }

    fn check_env(input: &str, expected: expect_test::Expect, env: &mut Env, tyenv: &mut TyEnv) {
        expected.assert_eq(
            &term_to_string(
                &eval(&parse(input, env).expect("Couldn't parse"), env, tyenv)
                    .expect("Couldn't evaluate"),
                &env,
            )
            .expect("Couldn't stringify"),
        );
    }

    fn old_check_env(lt: LTerm, expected: LTerm, env: &mut Env, tyenv: &mut TyEnv) {
        actual_check(lt, expected, env, tyenv);
    }

    fn actual_check(lt: LTerm, expected: LTerm, env: &mut Env, tyenv: &mut TyEnv) {
        let eval_res = eval(&lt, env, tyenv).expect("Could not evaluate");
        assert_eq!(eval_res, expected);
    }

    /// Evaluating a variable, returns the abstraction pointed to by the variable
    #[test]
    fn eval_variable() -> Result<()> {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        let id = parse("λx:Bool.x", &mut env)?;
        let ty = type_of(&id, &mut env, &mut tyenv)?;
        env.insert_term("id", &id)?;
        env.insert_type("id", &ty)?;

        old_check_env(parse("id", &mut env)?, id, &mut env, &mut tyenv);
        Ok(())
    }

    /// Evaluating an abstraction, returns the abstraction
    #[test]
    fn eval_abstraction() {
        check("λx:Bool.x", expect![["λx:Bool.x"]]);
    }

    #[test]
    fn application_abstraction_to_abstraction() -> Result<()> {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        let id = parse("λx:Bool.x", &mut env)?;
        let apply_fn = parse("λf:Bool → Bool.λb:Bool.f b", &mut env)?;
        let ty = type_of(&id, &mut env, &mut tyenv)?;
        env.insert_term("id", &id)?;
        env.insert_type("id", &ty)?;
        let ty = type_of(&apply_fn, &mut env, &mut tyenv)?;
        env.insert_term("applyfn", &apply_fn)?;
        env.insert_type("applyfn", &ty)?;
        check_env(
            "applyfn id",
            expect![["λb:Bool.(λx:Bool.x) b"]],
            &mut env,
            &mut tyenv,
        );

        Ok(())
    }

    #[test]
    fn eval_booleans() -> Result<()> {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        let tru = parse("λt:Bool.λf:Bool.t", &mut env)?;
        let ty = type_of(&tru, &mut env, &mut tyenv)?;
        env.insert_term("tru", &tru)?;
        env.insert_type("tru", &ty)?;
        // λt.λf.f
        let fls = parse("λt:Bool.λf:Bool.f", &mut env)?;
        let ty = type_of(&fls, &mut env, &mut tyenv)?;
        env.insert_term("fls", &fls)?;
        env.insert_type("fls", &ty)?;
        // λb.λc. b c false
        let and = parse("λb:Bool.λc:Bool.if b then c else false", &mut env)?;
        let ty = type_of(&and, &mut env, &mut tyenv)?;
        env.insert_term("and", &and)?;
        env.insert_type("and", &ty)?;

        check_env("and true true", expect![["true"]], &mut env, &mut tyenv);
        check_env("and true false", expect![["false"]], &mut env, &mut tyenv);
        check_env("and false true", expect![["false"]], &mut env, &mut tyenv);
        check_env("and false false", expect![["false"]], &mut env, &mut tyenv);

        // λb. b false true
        let not = parse("λb:Bool. if b then false else true", &mut env)?;
        let ty = type_of(&not, &mut env, &mut tyenv)?;
        env.insert_term("not", &not)?;
        env.insert_type("not", &ty)?;

        check_env("not true", expect![["false"]], &mut env, &mut tyenv);
        check_env("not false", expect![["true"]], &mut env, &mut tyenv);

        // λb.λc. b true c
        let or = parse("λb:Bool.λc:Bool.if b then true else c", &mut env)?;
        let ty = type_of(&or, &mut env, &mut tyenv)?;
        env.insert_term("or", &or)?;
        env.insert_type("or", &ty)?;

        check_env("or true true", expect![["true"]], &mut env, &mut tyenv);
        check_env("or true false", expect![["true"]], &mut env, &mut tyenv);
        check_env("or false true", expect![["true"]], &mut env, &mut tyenv);
        check_env("or false false", expect![["false"]], &mut env, &mut tyenv);

        let eq = parse("λb1:Bool.λb2:Bool.if b1 then b2 else not b2", &mut env)?;
        let ty = type_of(&eq, &mut env, &mut tyenv)?;
        env.insert_term("eq", &eq)?;
        env.insert_type("eq", &ty)?;
        check_env("eq true true", expect![["true"]], &mut env, &mut tyenv);
        check_env("eq false true", expect![["false"]], &mut env, &mut tyenv);
        check_env("eq true false", expect![["false"]], &mut env, &mut tyenv);
        check_env("eq false false", expect![["true"]], &mut env, &mut tyenv);

        let eq = parse("λb1:Bool.λb2:Bool.not (eq b1 b2)", &mut env)?;
        let ty = type_of(&eq, &mut env, &mut tyenv)?;
        env.insert_term("neq", &eq)?;
        env.insert_type("neq", &ty)?;
        check_env("neq true true", expect![["false"]], &mut env, &mut tyenv);
        check_env("neq false true", expect![["true"]], &mut env, &mut tyenv);
        check_env("neq true false", expect![["true"]], &mut env, &mut tyenv);
        check_env("neq false false", expect![["false"]], &mut env, &mut tyenv);

        Ok(())
    }

    #[test]
    fn eval_shifting() -> Result<()> {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        let tru = parse("λt:Bool.λf:Bool.t", &mut env)?;
        let ty = type_of(&tru, &mut env, &mut tyenv)?;
        env.insert_term("tru", &tru)?;
        env.insert_type("tru", &ty)?;

        let id = parse("λx:Bool.x", &mut env)?;
        let ty = type_of(&id, &mut env, &mut tyenv)?;
        env.insert_term("id", &id)?;
        env.insert_type("id", &ty)?;

        let id_shifted = shift(&id, 1)?;
        // Shouldn't touch id
        assert_eq!(id_shifted, id);

        let r#const = parse("λx:Bool.tru", &mut env)?;
        let const_shifted = shift(&r#const, 1)?;
        // Should shift true from 1 → 2
        expect![[r#"Term { span: Span { lo: 0, hi: 12 }, kind: Abstraction(Symbol("x"), Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Term { span: Span { lo: 0, hi: 12 }, kind: Variable(2) }) }"#]].assert_eq(&format!("{:?}", const_shifted));

        let test = parse("tru id", &mut env)?;
        let test_shifted = shift_above(&test, 3, 1)?;
        expect![[r#"Term { span: Span { lo: 0, hi: 6 }, kind: Application(Term { span: Span { lo: 0, hi: 6 }, kind: Variable(0) }, Term { span: Span { lo: 0, hi: 6 }, kind: Variable(4) }) }"#]].assert_eq(&format!("{:?}", test_shifted));
        expect![[r#"Term { span: Span { lo: 0, hi: 6 }, kind: Application(Term { span: Span { lo: 0, hi: 3 }, kind: Variable(0) }, Term { span: Span { lo: 4, hi: 6 }, kind: Variable(1) }) }"#]].assert_eq(&format!("{:?}", test));

        // ↑²(λ.λ.1 (0 2))
        let book_example_1 = parse("λx:Bool.λy:Bool.x (y tru)", &mut env)?;
        let b_ex_1_shifted = shift(&book_example_1, 2)?;
        // Expected λ.λ.1 (0 4)
        expect![[r#"Term { span: Span { lo: 0, hi: 27 }, kind: Abstraction(Symbol("x"), Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Term { span: Span { lo: 9, hi: 27 }, kind: Abstraction(Symbol("y"), Ty { span: Span { lo: 13, hi: 17 }, kind: Bool }, Term { span: Span { lo: 18, hi: 27 }, kind: Application(Term { span: Span { lo: 0, hi: 27 }, kind: Variable(1) }, Term { span: Span { lo: 20, hi: 27 }, kind: Application(Term { span: Span { lo: 0, hi: 27 }, kind: Variable(0) }, Term { span: Span { lo: 0, hi: 27 }, kind: Variable(4) }) }) }) }) }"#]].assert_eq(&format!("{:?}", b_ex_1_shifted));

        // ↑²(λ.0 1 (λ. 0 1 2))
        let book_example_2 = parse("λx:Bool.x tru (λy:Bool.y x tru)", &mut env)?;
        let b_ex_2_shifted = shift(&book_example_2, 2)?;
        // Expected λ.0 3 (λ. 0 1 4)
        expect![[r#"Term { span: Span { lo: 0, hi: 33 }, kind: Abstraction(Symbol("x"), Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Term { span: Span { lo: 9, hi: 33 }, kind: Application(Term { span: Span { lo: 9, hi: 14 }, kind: Application(Term { span: Span { lo: 0, hi: 33 }, kind: Variable(0) }, Term { span: Span { lo: 0, hi: 33 }, kind: Variable(3) }) }, Term { span: Span { lo: 15, hi: 33 }, kind: Abstraction(Symbol("y"), Ty { span: Span { lo: 20, hi: 24 }, kind: Bool }, Term { span: Span { lo: 25, hi: 32 }, kind: Application(Term { span: Span { lo: 25, hi: 28 }, kind: Application(Term { span: Span { lo: 0, hi: 33 }, kind: Variable(0) }, Term { span: Span { lo: 0, hi: 33 }, kind: Variable(1) }) }, Term { span: Span { lo: 0, hi: 33 }, kind: Variable(4) }) }) }) }) }"#]].assert_eq(&format!("{:?}", b_ex_2_shifted));
        Ok(())
    }

    #[test]
    fn eval_de_bruijn_indices() -> Result<()> {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        let t = parse("λt:Bool.λf:Bool.t", &mut env)?;
        assert_eq!(term_to_string(&t, &env)?, "λt:Bool.λf:Bool.t");

        let t = parse("λx:Bool.x x", &mut env)?;
        assert_eq!(term_to_string(&t, &env)?, "λx:Bool.x x");

        let t = parse("λx:Bool.λx:Bool.x", &mut env)?;
        assert_eq!(term_to_string(&t, &env)?, "λx:Bool.λx':Bool.x'");

        let t = parse("(λx:Bool → Bool.λy:Bool.x y) λx:Bool.x", &mut env)?;
        let t = eval(&t, &mut env, &mut tyenv)?;
        assert_eq!(term_to_string(&t, &env)?, "λy:Bool.(λx:Bool.x) y");

        let id = parse("λx:Bool.x", &mut env)?;
        let ty = type_of(&id, &mut env, &mut tyenv)?;
        env.insert_term("id", &id)?;
        env.insert_type("id", &ty)?;

        let t = parse(
            "(λz:Bool → Bool.λid:(Bool → Bool) → Bool.id z) λz:Bool.id z",
            &mut env,
        )?;
        let t = eval(&t, &mut env, &mut tyenv)?;
        assert_eq!(
            term_to_string(&t, &env)?,
            "λid':(Bool → Bool) → Bool.id' λz:Bool.id z"
        );
        Ok(())
    }

    #[test]
    fn eval_nat() {
        check("0", expect![["0"]]);
        check("1", expect![[r#"1"#]]);
        check("iszero 0", expect![[r#"true"#]]);
        check("iszero succ 0", expect![[r#"false"#]]);
        check("iszero pred succ 0", expect![[r#"true"#]]);
        check("pred 0", expect![[r#"0"#]]);
        check("pred succ 0", expect![[r#"0"#]]);
        check("pred pred pred pred 0", expect![[r#"0"#]]);
        check("succ succ pred 0", expect![[r#"2"#]]);
        check("pred 3", expect![[r#"2"#]]);
        check("(λx:Nat.iszero pred x) 0", expect![[r#"true"#]]);
        check("(λx:Nat.iszero pred x) 1", expect![[r#"true"#]]);
        check("(λx:Nat.iszero pred x) 2", expect![[r#"false"#]]);
    }

    #[test]
    fn eval_unit() {
        check("unit", expect![[r#"unit"#]]);
        check("(λx:Nat.unit)3", expect![[r#"unit"#]]);
        check("(λx:Unit.true)unit", expect![[r#"true"#]]);
    }

    #[test]
    fn eval_ascription() {
        check("true as Bool", expect![[r#"true"#]]);
        check("0 as Nat", expect![[r#"0"#]]);
        check("(λx:Bool.x) as Bool → Bool", expect![[r#"λx:Bool.x"#]]);
    }

    #[test]
    fn eval_let_binding() {
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

        // Pattern matching works!
        check("let {x} = {true} in x", expect![[r#"true"#]]);
        check(
            "let {f=f, l=l} = {f=0, l=true} in succ f",
            expect![[r#"1"#]],
        );
        check(
            "let {f=f, l=l} = {f={0, true}, l={unit}} in f",
            expect![[r#"{0, true}"#]],
        );
        check(
            "let {f=f, l=l} = {f={0, true}, l={unit}} in l",
            expect![[r#"{unit}"#]],
        );
        check(
            "let {f={x, y}, l=l} = {f={0, true}, l={unit}} in x",
            expect![[r#"0"#]],
        );
        check(
            "let {f={x, y}, l=l} = {f={0, true}, l={unit}} in y",
            expect![[r#"true"#]],
        );
        check(
            "let {{x, y}, {z, a}} = {{true, false}, {0, unit}} in {{a, z}, {y, x}}",
            expect![[r#"{{unit, 0}, {false, true}}"#]],
        );
        check(
            "let {x} = {true} in λ_:Bool.x",
            expect![[r#"λ_:Bool.true"#]],
        );
    }

    #[test]
    fn eval_record() {
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

    #[test]
    fn eval_descriptions() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        check_env("let a = true;", expect![[r#"unit"#]], &mut env, &mut tyenv);
        check_env("a", expect![[r#"true"#]], &mut env, &mut tyenv);

        check_env(
            "let {b, c} = {false, 0};",
            expect![[r#"unit"#]],
            &mut env,
            &mut tyenv,
        );
        check_env("b", expect![[r#"false"#]], &mut env, &mut tyenv);
        check_env("c", expect![[r#"0"#]], &mut env, &mut tyenv);

        check_env(
            "let {l=d, r=e} = {l={unit}, r=λx:Bool.x};",
            expect![[r#"unit"#]],
            &mut env,
            &mut tyenv,
        );
        check_env("d", expect![[r#"{unit}"#]], &mut env, &mut tyenv);
        check_env("e", expect![[r#"λx:Bool.x"#]], &mut env, &mut tyenv);
        check_env(
            "let f = true; f",
            expect![[r#"true"#]],
            &mut env,
            &mut tyenv,
        );
    }

    #[test]
    fn eval_variants() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        check_env(
            "type MaybeNat = <some:Nat, none:Unit>;",
            expect![[r#"unit"#]],
            &mut env,
            &mut tyenv,
        );
        check_env(
            "<some=pred succ 0> as MaybeNat",
            expect![[r#"<some=0>"#]],
            &mut env,
            &mut tyenv,
        );
    }

    #[test]
    fn eval_case_of() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        check_env(
            "type MaybeNat = <some:Nat, none:Unit>;",
            expect![[r#"unit"#]],
            &mut env,
            &mut tyenv,
        );
        //check_env(
        //    "let is_some = λs:MaybeNat.case s of <some=_> => true | _ => false;",
        //    expect![[r#"unit"#]],
        //    &mut env,
        //    &mut tyenv,
        //);
        //expect![[r#"MaybeNat → Bool"#]].assert_eq(&format!("{}", env.get_type("is_some").unwrap()));

        //check_env(
        //    "case <some=0> of <some=x> => <some=succ x>",
        //    expect![[r#"<some=1>"#]],
        //    &mut env
        //, &mut tyenv);

        //check_env(
        //    "is_some <some=0> as MaybeNat",
        //    expect![[r#"true"#]],
        //    &mut env,
        //    &mut tyenv,
        //);

        //check_env(
        //    "is_some <none=unit> as MaybeNat",
        //    expect![[r#"false"#]],
        //    &mut env,
        //    &mut tyenv,
        //);

        // Test correct term_map
        check_env(
            "let f = λmn:MaybeNat.case mn of
                                <some=n> => <some=succ n> as MaybeNat
                                | <none=u> => <none=u> as MaybeNat;",
            expect![[r#"unit"#]],
            &mut env,
            &mut tyenv,
        );

        check_env(
            "f <none=unit>",
            expect![[r#"<none=unit>"#]],
            &mut env,
            &mut tyenv,
        );

        //check_env(
        //    "(λm:MaybeNat. case m of _ => true) <none=unit> as MaybeNat",
        //    expect![["true"]],
        //    &mut env,
        //    &mut tyenv,
        //);

        //check_env(
        //    "(λm:MaybeNat. case m of _ => true) <none=unit> as MaybeNat",
        //    expect![["true"]],
        //    &mut env,
        //    &mut tyenv,
        //);

        //check_env(
        //    "let a = 3 in case <some=0> as MaybeNat of _ => a",
        //    expect![["3"]],
        //    &mut env,
        //    &mut tyenv,
        //);
    }

    #[test]
    fn eval_fix() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();

        check_env(
            r#"let ff = λie:Nat → Bool.
                         λx:Nat.
                          if iszero x then true
                          else if iszero (pred x) then false
                          else ie (pred (pred x));"#,
            expect![[r#"unit"#]],
            &mut env,
            &mut tyenv,
        );

        check_env(
            r#"let iseven = fix ff;"#,
            expect![[r#"unit"#]],
            &mut env,
            &mut tyenv,
        );

        check_env(r#"iseven 7"#, expect![[r#"false"#]], &mut env, &mut tyenv);

        check_env(r#"iseven 6"#, expect![[r#"true"#]], &mut env, &mut tyenv);
    }

    #[test]
    fn eval_letrec() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();

        check_env(
            r#"letrec iseven: Nat → Bool =
                λx:Nat.
                    if iszero x then true
                    else if iszero (pred x) then false
                    else iseven (pred (pred x))
                in iseven 7"#,
            expect![[r#"false"#]],
            &mut env,
            &mut tyenv,
        );

        check_env(
            r#"letrec sum: Nat → Nat → Nat =
                λa:Nat.λb:Nat.
                    if iszero a then b
                    else sum (pred a) (succ b);
                sum 10 10"#,
            expect![[r#"20"#]],
            &mut env,
            &mut tyenv,
        );
    }

    #[test]
    fn eval_lists() {
        check("nil[Bool]", expect![["nil[Bool]"]]);
        check("isnil[Bool] nil[Bool]", expect![["true"]]);
        check("cons[Nat] 0 nil[Nat]", expect![["cons[Nat] 0 nil[Nat]"]]);
        check("isnil[Nat] cons[Nat] 0 nil[Nat]", expect![["false"]]);
        check("head[Nat] cons[Nat] 0 nil[Nat]", expect![["0"]]);
        check("tail[Nat] cons[Nat] 0 nil[Nat]", expect![["nil[Nat]"]]);

        check(
            r#"
                letrec sum: Nat → Nat → Nat = λa:Nat.λb:Nat.
                             if iszero a then b
                             else sum (pred a) (succ b)
                in
                    letrec sum_list: (List Nat) → Nat = λl:List Nat.
                                      if isnil[Nat] l then 0
                                      else sum (head[Nat] l) (sum_list (tail[Nat] l))
                    in
                        sum_list(cons[Nat] 2 (cons[Nat] 1 (cons[Nat] 0 (nil[Nat]))))
            "#,
            expect![["3"]],
        );
    }

    #[test]
    fn eval_references() {
        check("ref 0", expect![["ref 0"]]);
        check("let a = ref 0; !a", expect![["0"]]);
        check("let a = ref 0; (a := 1; !a)", expect![["1"]]);

        // Aliasing
        check(
            r#"
            let r = ref 5;
            let s = r;
            (s := 20; !r)
            "#,
            expect![["20"]],
        );

        let mut env = base_env();
        let mut tyenv = TyEnv::new();

        check(
            r#"
            let c = ref 0;
            let incc = λx:Unit.(c := succ (!c); !c);
            let decc = λx:Unit.(c := pred (!c); !c);
            let o = {i=incc, d=decc};
            o.i unit
            "#,
            expect![["1"]],
        );

        check_env(
            r#"
            type NatArray = Ref (Nat → Nat);
            let newarray = λ_:Unit.ref (λn:Nat.0);
            let lookup = λa:NatArray.λn:Nat.(!a) n;
            let update = λa:NatArray.λm:Nat.λv:Nat.
                        let oldf = !a in
                        a := (λn:Nat.if equal m n then v else oldf n);
            let array = newarray unit;
            "#,
            expect![["unit"]],
            &mut env,
            &mut tyenv,
        );

        check_env("lookup array 0", expect![[r#"0"#]], &mut env, &mut tyenv);

        check_env(
            "update array 1 5",
            expect![[r#"unit"#]],
            &mut env,
            &mut tyenv,
        );

        check_env("lookup array 1", expect![[r#"5"#]], &mut env, &mut tyenv);
    }
}
