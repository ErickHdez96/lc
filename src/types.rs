use crate::{env::TyEnv, term::Pattern, Env, Error, ErrorKind, LTerm, Span, Symbol, TermKind, TY};
use std::{collections::HashMap, fmt, rc::Rc};

type Result<T> = std::result::Result<T, Error>;

macro_rules! error {
    ($msg:expr, $($arg:expr),*; $span:expr) => {
        Error::new(format!($msg, $($arg),*), $span, ErrorKind::Type)
    };
    ($msg:expr; $span:expr) => {
        error!($msg,;$span)
    };
}

/// ```text
/// T ::=
///     Bool    type of booleans
///     Nat     type of natural numbers
///     A       base type
///     Unit    unit type
///     T → T   type of functions
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ty {
    pub span: Span,
    pub kind: TyKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyKind {
    /// Bool
    Bool,
    /// Nat
    Nat,
    /// Unit
    Unit,
    /// <id> (e.g. A, B, Option)
    Base(Symbol),
    /// T → T
    Abstraction(LTy, LTy),
    /// {lᵢ:Tᵢ}
    Record(
        HashMap<Symbol, LTy>,
        /** Original order of the keys */ Vec<Symbol>,
    ),
    /// <lᵢ:Tᵢ>
    Variant(HashMap<Symbol, LTy>, Vec<Symbol>),
    List(LTy),
}

pub type LTy = Rc<Ty>;

impl Ty {
    pub fn is_abstraction(&self) -> bool {
        matches!(self.kind, TyKind::Abstraction(_, _))
    }

    pub fn is_list(&self) -> bool {
        matches!(self.kind, TyKind::List(_))
    }
}

impl TyKind {
    pub fn is_abstraction(&self) -> bool {
        matches!(self, TyKind::Abstraction(_, _))
    }

    pub fn is_list(&self) -> bool {
        matches!(self, TyKind::List(_))
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl fmt::Display for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn symbol_to_record_key(s: Symbol) -> String {
            if s.as_str().parse::<u64>().is_ok() {
                String::new()
            } else {
                format!("{}:", s)
            }
        }

        match self {
            TyKind::Bool => write!(f, "Bool"),
            TyKind::Nat => write!(f, "Nat"),
            TyKind::Base(s) => s.fmt(f),
            TyKind::Unit => write!(f, "Unit"),
            TyKind::Abstraction(t1, t2) => {
                let (l_paren, r_paren) = if t1.is_abstraction() | t1.is_list() {
                    ("(", ")")
                } else {
                    ("", "")
                };
                write!(f, "{}{}{} → {}", l_paren, t1, r_paren, t2)
            }
            TyKind::Record(elems, keys) => {
                write!(
                    f,
                    "{{{}}}",
                    keys.iter()
                        .copied()
                        .map(|k| format!("{}{}", symbol_to_record_key(k), elems.get(&k).unwrap()))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TyKind::Variant(variants, keys) => {
                write!(
                    f,
                    "<{}>",
                    keys.iter()
                        .copied()
                        .map(|k| format!("{}:{}", k, variants.get(&k).unwrap()))
                        .collect::<Vec<_>>()
                        .join(", "),
                )
            }
            TyKind::List(ty) => write!(f, "List {}", ty),
        }
    }
}

pub fn type_of(type_t: &LTerm, env: &mut Env, tyenv: &mut TyEnv) -> Result<LTy> {
    match type_t.as_ref().kind {
        TermKind::True => Ok(TY![bool; type_t.span]),
        TermKind::False => Ok(TY![bool; type_t.span]),
        TermKind::Zero => Ok(TY![nat; type_t.span]),
        TermKind::Unit => Ok(TY![unit; type_t.span]),
        TermKind::Ascription(ref t, ref ty) => match type_of(t, env, tyenv)?.as_ref() {
            t if cmp_ty(&t.kind, &ty.kind, &tyenv) => Ok(ty.clone()),
            t => Err(error!("Expected type `{}`, got `{}`", ty, t; t.span)),
        },
        TermKind::Succ(ref t) | TermKind::Pred(ref t) => match &type_of(t, env, tyenv)?.as_ref() {
            t if cmp_ty(&t.kind, &TyKind::Nat, &tyenv) => Ok(TY![nat; type_t.span]),
            t => Err(error!("Expected type `Nat`, got `{}`", t; t.span)),
        },
        TermKind::IsZero(ref t) => match &type_of(t, env, tyenv)?.as_ref() {
            t if cmp_ty(&t.kind, &TyKind::Nat, &tyenv) => Ok(TY![bool; type_t.span]),
            t => Err(error!("Expected type `Nat`, got `{}`", t; t.span)),
        },
        TermKind::Abstraction(v, ref ty, ref body) => {
            let mut env = Env::with_parent(&env);
            env.insert_type(v, &ty)?;
            type_of(body, &mut env, tyenv).map(|body_ty| TY![abs ty, body_ty; type_t.span])
        }
        TermKind::Variable(idx) => env
            .get_type_from_index(idx)
            .ok_or_else(|| error!("Invalid de Bruijn index {}", idx; type_t.span)),
        TermKind::Application(ref t1, ref t2) => {
            // If t1 is `let x = t;` or `type A = T;`, we can ignore the result
            // of evaluating it (i.e. Unit) and just return `t2`.
            let ignore_t1 = t1.is_definition();
            let t1_ty = type_of(t1, env, tyenv)?;
            let t2_ty = type_of(t2, env, tyenv)?;

            match t1_ty.as_ref().kind {
                TyKind::Abstraction(ref t11_ty, ref t12_ty) => {
                    if cmp_ty(&t11_ty.kind, &t2_ty.kind, &tyenv) {
                        Ok(t12_ty.clone())
                    } else {
                        Err(error!("Expected type `{}`, got `{}`", t11_ty, t2_ty; t2.span))
                    }
                }
                _ if ignore_t1 => Ok(t2_ty),
                _ => Err(error!("Expected an abstraction, got `{}`", t1_ty; t1.span)),
            }
        }
        TermKind::If(ref cond, ref then, ref else_b) => {
            match &type_of(cond, env, tyenv)?.as_ref().kind {
                TyKind::Bool => {
                    let then_ty = type_of(then, env, tyenv)?;
                    let else_ty = type_of(else_b, env, tyenv)?;

                    if cmp_ty(&then_ty.kind, &else_ty.kind, &tyenv) {
                        Ok(else_ty)
                    } else {
                        Err(error!(
                            "Arms of conditional have different types: `{}`, and `{}`",
                            then_ty, else_ty; type_t.span
                        ))
                    }
                }
                ty => Err(error!("Guard conditional expects a Bool, got `{}`", ty; cond.span)),
            }
        }
        TermKind::Let(ref p, ref t1, ref t2) => {
            let t1 = type_of(t1, env, tyenv)?;
            let mut env = resolve_match(p, &t1, &env, type_t.span)?;
            type_of(t2, &mut env, tyenv)
        }
        TermKind::Record(ref elems, ref keys) => keys
            .iter()
            .cloned()
            .map(|k| type_of(elems.get(&k).unwrap(), env, tyenv).map(|e| (k, e)))
            .collect::<Result<HashMap<_, _>>>()
            .map(|elems| {
                Rc::new(Ty {
                    kind: TyKind::Record(elems, keys.clone()),
                    span: type_t.span,
                })
            }),
        TermKind::Projection(ref record, elem) => {
            let record = type_of(record, env, tyenv)?;
            match record.as_ref().kind {
                TyKind::Record(ref elems, _) => match elems.get(&elem) {
                    Some(elem) => Ok(elem.clone()),
                    None => Err(error!(
                        "The element `{}` does not exist on the record `{}`",
                        elem, record; type_t.span
                    )),
                },
                _ => Err(error!("Only a record can be projected, got `{}`", record; record.span)),
            }
        }
        TermKind::VariableDefinition(ref p, ref t) => {
            let ty = match type_of(&t, env, tyenv) {
                ty @ Ok(_) => ty,
                e @ Err(_) => {
                    remove_pattern_matches(p, env);
                    e
                }
            }?;
            resolve_match_mut(p, &ty, env, type_t.span)?;
            Ok(TY![unit; type_t.span])
        }
        TermKind::TypeDefinition(v, ref ty) => {
            tyenv.insert(v, ty)?;
            Ok(TY![unit; type_t.span])
        }
        TermKind::Variant(label, ref term, ref ty) => {
            let term_ty = type_of(term, env, tyenv)?;
            match &eval_ty(&ty, &tyenv).kind {
                TyKind::Variant(ref variants, _) => match variants.get(&label) {
                    Some(expected_ty) => {
                        if cmp_ty(&term_ty.kind, &expected_ty.kind, &tyenv) {
                            Ok(Rc::clone(ty))
                        } else {
                            Err(
                                error!("Variant `{}` expects type `{}`, got `{}`", ty, expected_ty, term_ty; term_ty.span),
                            )
                        }
                    }
                    None => Err(
                        error!("The label `{}` is not a variant of `{}`", label, ty; type_t.span),
                    ),
                },
                _ => Err(error!("Expected a variant type, got `{}`", ty; ty.span)),
            }
        }
        TermKind::Case(ref value, ref branches, _) => {
            let value_ty = type_of(value, env, tyenv)?;
            let evald_value_ty = eval_ty(&value_ty, &tyenv);
            let variants = if let TyKind::Variant(ref variants, _) = evald_value_ty.kind {
                variants
            } else {
                return Err(error!("Expected a variant type, got `{}`", value_ty; value_ty.span));
            };

            let mut ret_ty: Option<LTy> = None;

            for (variant, (var, term)) in branches {
                let var_ty = match variants.get(variant) {
                    Some(var_ty) => var_ty,
                    None => {
                        return Err(
                            error!("The label `{}` is not a variant of `{}`", variant, value_ty; type_t.span),
                        )
                    }
                };

                let mut env = Env::with_parent(&env);
                env.insert_type(*var, var_ty)?;
                let term_ty = type_of(term, &mut env, tyenv)?;
                if let Some(ret_ty) = &ret_ty {
                    if !cmp_ty(&ret_ty.kind, &term_ty.kind, &tyenv) {
                        return Err(
                            error!("Expected type `{}`, got `{}`", ret_ty, term_ty; term_ty.span),
                        );
                    }
                } else {
                    ret_ty = Some(term_ty);
                }
            }

            if branches.len() < variants.len() {
                for variant in variants.keys() {
                    if branches.get(variant).is_none() {
                        return Err(error!("The label `{}` is not covered", variant; type_t.span));
                    }
                }
            }

            // If there are no case branches, that is a parser error
            Ok(ret_ty.expect("at least one case branch"))
        }
        TermKind::Fix(ref t) => {
            let t_ty = type_of(t, env, tyenv)?;
            match &t_ty.kind {
                TyKind::Abstraction(par_ty, ret_ty) => {
                    if cmp_ty(&par_ty.kind, &ret_ty.kind, tyenv) {
                        Ok(Rc::clone(ret_ty))
                    } else {
                        Err(
                            error!("Fix expects return type to be `{}`, got `{}", par_ty, ret_ty; type_t.span),
                        )
                    }
                }
                _ => Err(error!("Fix expects an abstraction, got `{}`", t_ty; type_t.span)),
            }
        }
        TermKind::Nil(ref ty) => Ok(Rc::new(Ty {
            span: type_t.span,
            kind: TyKind::List(Rc::clone(ty)),
        })),
        TermKind::Cons(ref t1, ref t2, ref ty) => {
            let t1_ty = type_of(t1, env, tyenv)?;
            let t2_ty = type_of(t2, env, tyenv)?;

            if !cmp_ty(&t1_ty.kind, &ty.kind, tyenv) {
                return Err(error!("Expected type `{}`, got `{}", ty, t1_ty; t1.span));
            }

            match &t2_ty.kind {
                TyKind::List(t2_ty) if cmp_ty(&t2_ty.kind, &ty.kind, tyenv) => Ok(Rc::new(Ty {
                    span: type_t.span,
                    kind: TyKind::List(Rc::clone(ty)),
                })),
                t2_ty => Err(error!("Expected type `List {}`, got `{}`", ty, t2_ty; t2.span)),
            }
        }
        TermKind::IsNil(ref t, ref ty) => {
            let t_ty = type_of(t, env, tyenv)?;

            match &t_ty.kind {
                TyKind::List(t_ty) if cmp_ty(&t_ty.kind, &ty.kind, tyenv) => {
                    Ok(TY![bool; type_t.span])
                }
                _ => Err(error!("Expected type `List {}`, got `{}", ty, t_ty; t.span)),
            }
        }
        TermKind::Head(ref t, ref ty) => {
            let t_ty = type_of(t, env, tyenv)?;

            match &t_ty.kind {
                TyKind::List(t_ty) if cmp_ty(&t_ty.kind, &ty.kind, tyenv) => Ok(Rc::clone(ty)),
                _ => Err(error!("Expected type `List {}`, got `{}", ty, t_ty; t.span)),
            }
        }
        TermKind::Tail(ref t, ref ty) => {
            let t_ty = type_of(t, env, tyenv)?;

            match &t_ty.kind {
                TyKind::List(t_ty) if cmp_ty(&t_ty.kind, &ty.kind, tyenv) => Ok(Rc::new(Ty {
                    span: type_t.span,
                    kind: TyKind::List(Rc::clone(ty)),
                })),
                _ => Err(error!("Expected type `List {}`, got `{}", ty, t_ty; t.span)),
            }
        }
    }
}

pub fn eval_ty(t1: &LTy, tyenv: &TyEnv) -> LTy {
    match &t1.as_ref().kind {
        TyKind::Base(name) => match tyenv.get(*name) {
            Some(ref ty) => eval_ty(ty, tyenv),
            None => Rc::clone(t1),
        },
        _ => Rc::clone(t1),
    }
}

pub fn cmp_ty<'a>(t1: &'a TyKind, t2: &'a TyKind, tyenv: &TyEnv) -> bool {
    match (t1, t2) {
        (TyKind::Bool, TyKind::Bool) => true,
        (TyKind::Nat, TyKind::Nat) => true,
        (TyKind::Unit, TyKind::Unit) => true,
        (TyKind::Abstraction(p1, r1), TyKind::Abstraction(p2, r2)) => {
            cmp_ty(&p1.kind, &p2.kind, tyenv) && cmp_ty(&r1.kind, &r2.kind, tyenv)
        }
        (TyKind::Record(ref recs1, ref keys1), TyKind::Record(ref recs2, ref keys2)) => {
            if keys1.len() != keys2.len() {
                return false;
            }
            for (k1, k2) in keys1.iter().zip(keys2.iter()) {
                if k1 != k2 {
                    return false;
                }
                if !cmp_ty(
                    &recs1.get(k1).unwrap().kind,
                    &recs2.get(k1).unwrap().kind,
                    &tyenv,
                ) {
                    return false;
                }
            }
            true
        }
        (TyKind::List(ref t1), TyKind::List(ref t2)) => cmp_ty(&t1.kind, &t2.kind, tyenv),
        (TyKind::Base(s1), TyKind::Base(s2)) if s1 == s2 => true,
        (TyKind::Base(s1), TyKind::Base(s2)) => {
            let s1 = tyenv.get(*s1);
            let s2 = tyenv.get(*s2);
            match (s1, s2) {
                (Some(ty1), Some(ty2)) => cmp_ty(&ty1.kind, &ty2.kind, &tyenv),
                _ => false,
            }
        }
        (TyKind::Base(b), t) | (t, TyKind::Base(b)) => match tyenv.get(*b) {
            Some(b_ty) => cmp_ty(&b_ty.kind, t, tyenv),
            _ => false,
        },
        _ => false,
    }
}

fn resolve_match<'a>(p: &Pattern, t: &LTy, env: &'a Env, p_span: Span) -> Result<Env<'a>> {
    let mut env = Env::with_parent(&env);
    resolve_match_mut(p, t, &mut env, p_span)?;
    Ok(env)
}

fn remove_pattern_matches(p: &Pattern, env: &mut Env) {
    match p {
        Pattern::Var(s) => {
            env.remove_symbol(*s);
        }
        Pattern::Record(ref recs, _) => {
            for pat in recs.values() {
                remove_pattern_matches(pat, env);
            }
        }
    }
}

fn resolve_match_mut(p: &Pattern, t: &LTy, mut env: &mut Env, p_span: Span) -> Result<()> {
    match p {
        Pattern::Var(s) => {
            env.insert_type(*s, t)?;
            Ok(())
        }
        Pattern::Record(recs, keys) => match t.as_ref().kind {
            TyKind::Record(ref trecs, ref tkeys) => {
                if tkeys.len() > keys.len() {
                    let mut span_iter = tkeys[keys.len()..]
                        .iter()
                        .map(|k| trecs.get(&k).unwrap().span);
                    let start = span_iter.next().unwrap();
                    let p_span = span_iter.fold(start, |acc, cur| acc.with_hi(cur.hi));
                    // To probably do: Display missing tuple keys better
                    return Err(error!(
                        "The keys `{}` are not matched against",
                        tkeys[keys.len()..]
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ");
                        p_span
                    ));
                }

                for (i, key) in keys.iter().copied().enumerate() {
                    // The keys must be in the same order
                    match tkeys.get(i).copied() {
                        Some(k) if k == key => {
                            resolve_match_mut(
                                recs.get(&key).unwrap(),
                                trecs.get(&key).unwrap(),
                                &mut env,
                                p_span,
                            )?;
                        }
                        Some(_) if trecs.get(&key).is_some() => {
                            return Err(
                                error!("Match keys must follow the same order as the record"; p_span),
                            );
                        }
                        _ => {
                            return Err(
                                error!("The key `{}` does not exist in the record", key; p_span),
                            );
                        }
                    }
                }

                Ok(())
            }
            _ => Err(error!("Only records can be pattern matched"; p_span)),
        },
    }
}

#[macro_export]
macro_rules! TY {
(bool; $span:expr) => {
    Rc::new(Ty { kind: TyKind::Bool, span: $span.into() })
};
(nat; $span:expr) => {
    Rc::new(Ty { kind: TyKind::Nat, span: $span.into() })
};
(unit; $span:expr) => {
        Rc::new(Ty { kind: TyKind::Unit, span: $span.into() })
    };
    (base $s:expr; $span:expr) => {
        Rc::new(Ty { kind: TyKind::Base($s.into()), span: $span.into() })
    };
    (abs $t1:expr, $t2:expr; $span:expr) => {
        Rc::new(Ty { kind: TyKind::Abstraction($t1.clone(), $t2.clone()), span: $span.into() })
    };
    (record $($term:expr),*; $span:expr) => {
        Rc::new(Ty { kind: TyKind::Record(vec![$($term.clone()),*]), span: $span.into() })
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;
    use expect_test::expect;

    const SPAN: Span = Span::new(0, 1);

    fn check(input: &str, expected: expect_test::Expect) {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        expected.assert_eq(&format!(
            "{}",
            &type_of(
                &parse(input, &mut env).expect("Couldn't parse"),
                &mut env,
                &mut tyenv
            )
            .expect("Couldn't evaluate")
        ));
    }

    fn check_parse_error(input: &str, expected: expect_test::Expect) {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        expected.assert_eq(
            &type_of(
                &parse(input, &mut env).expect("Couldn't parse"),
                &mut env,
                &mut tyenv,
            )
            .expect_err("Shouldn't type check correctly")
            .to_string(),
        );
    }

    fn check_env(input: &str, expected: expect_test::Expect, env: &mut Env, tyenv: &mut TyEnv) {
        expected.assert_eq(&format!(
            "{}",
            &type_of(&parse(input, env).expect("Couldn't parse"), env, tyenv)
                .expect("Couldn't evaluate")
        ));
    }

    fn check_parse_error_env(
        input: &str,
        expected: expect_test::Expect,
        env: &mut Env,
        tyenv: &mut TyEnv,
    ) {
        expected.assert_eq(
            &type_of(&parse(input, env).expect("Couldn't parse"), env, tyenv)
                .expect_err("Shouldn't type check correctly")
                .to_string(),
        );
    }

    #[test]
    fn typecheck_constant_types() {
        check("true", expect![[r#"Bool"#]]);
    }

    #[test]
    fn typecheck_types() {
        check("λx:Bool.x", expect![[r#"Bool → Bool"#]]);
        // (Bool → Bool) → Bool → Bool
        check(
            "λf:Bool→Bool.λb:Bool.f b",
            expect![[r#"(Bool → Bool) → Bool → Bool"#]],
        );
    }

    #[test]
    fn typecheck_if() {
        check(
            "if (λx:Bool.x) true then λx:Bool.false else λx:Bool.x",
            expect![[r#"Bool → Bool"#]],
        );
    }

    #[test]
    fn error_wrong_application_types() {
        check_parse_error(
            "(λx:Bool.x)(λx:Bool.x)",
            expect![[r#"[12-24]TypeError: Expected type `Bool`, got `Bool → Bool`"#]],
        );
        check_parse_error(
            "true λx:Bool.x",
            expect![[r#"[0-4]TypeError: Expected an abstraction, got `Bool`"#]],
        );
        check_parse_error(
            "λf:Bool → Bool.λx:Bool.x f",
            expect![[r#"[27-28]TypeError: Expected an abstraction, got `Bool`"#]],
        );
    }

    #[test]
    fn error_wrong_if_types() {
        check_parse_error(
            "if λx:Bool.x then true else false",
            expect![[r#"[3-13]TypeError: Guard conditional expects a Bool, got `Bool → Bool`"#]],
        );
        check_parse_error(
            "if true then true else λx:Bool.x",
            expect![[
                r#"[0-33]TypeError: Arms of conditional have different types: `Bool`, and `Bool → Bool`"#
            ]],
        );
    }

    #[test]
    fn print_correct_precedence() {
        let ty = TY![abs TY![bool; SPAN], TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN]; SPAN];
        // → is right associative
        assert_eq!(ty.to_string(), "Bool → Bool → Bool");

        let ty = TY![abs TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN], TY![bool; SPAN]; SPAN];
        assert_eq!(ty.to_string(), "(Bool → Bool) → Bool");
    }

    #[test]
    fn typecheck_base_types() {
        check("λx:A.x", expect![[r#"A → A"#]]);
        check("λx:B.x", expect![[r#"B → B"#]]);
        check("λf:A → A.λx:A. f(f(x))", expect![[r#"(A → A) → A → A"#]]);
    }

    #[test]
    fn typecheck_nat() {
        check("0", expect![[r#"Nat"#]]);
        check("5", expect![[r#"Nat"#]]);
        check("pred 0", expect![[r#"Nat"#]]);
        check("pred pred pred 0", expect![[r#"Nat"#]]);
        check("succ 0", expect![[r#"Nat"#]]);
        check("succ succ succ 0", expect![[r#"Nat"#]]);
        check("pred succ 0", expect![[r#"Nat"#]]);
        check("iszero 0", expect![[r#"Bool"#]]);
        check("iszero pred succ 0", expect![[r#"Bool"#]]);

        // is_greater_than_one
        check("λx:Nat.iszero pred x", expect![[r#"Nat → Bool"#]]);
        check("(λx:Nat.iszero pred x) 0", expect![[r#"Bool"#]]);
    }

    #[test]
    fn error_typecheck_nat() {
        check_parse_error(
            "pred true",
            expect![[r#"[5-9]TypeError: Expected type `Nat`, got `Bool`"#]],
        );
        check_parse_error(
            "succ true",
            expect![[r#"[5-9]TypeError: Expected type `Nat`, got `Bool`"#]],
        );
        check_parse_error(
            "succ succ succ pred succ true",
            expect![[r#"[25-29]TypeError: Expected type `Nat`, got `Bool`"#]],
        );
        check_parse_error(
            "iszero true",
            expect![[r#"[7-11]TypeError: Expected type `Nat`, got `Bool`"#]],
        );
        check_parse_error(
            "pred iszero 0",
            expect![[r#"[5-13]TypeError: Expected type `Nat`, got `Bool`"#]],
        );
        check_parse_error(
            "pred iszero true",
            expect![[r#"[12-16]TypeError: Expected type `Nat`, got `Bool`"#]],
        );
        check_parse_error(
            "if 0 then true else false",
            expect![[r#"[3-4]TypeError: Guard conditional expects a Bool, got `Nat`"#]],
        );
        check_parse_error(
            "if iszero pred succ 0 then true else 0",
            expect![[
                r#"[0-38]TypeError: Arms of conditional have different types: `Bool`, and `Nat`"#
            ]],
        );
    }

    #[test]
    fn typecheck_unit() {
        check("unit", expect![[r#"Unit"#]]);
        check("λx:Unit.x", expect![[r#"Unit → Unit"#]]);
        check("λx:Nat.unit", expect![[r#"Nat → Unit"#]]);
        check("(λ_:Unit.unit)unit", expect![[r#"Unit"#]]);
    }

    #[test]
    fn error_typecheck_unit() {
        check_parse_error(
            "iszero unit",
            expect![[r#"[7-11]TypeError: Expected type `Nat`, got `Unit`"#]],
        );
        check_parse_error(
            "(λx:Nat.unit) unit",
            expect![[r#"[15-19]TypeError: Expected type `Nat`, got `Unit`"#]],
        );
    }

    #[test]
    fn typecheck_ascription() {
        check("true as Bool", expect![[r#"Bool"#]]);
        check("0 as Nat", expect![[r#"Nat"#]]);
        check("(λx:Bool.x) as Bool → Bool", expect![[r#"Bool → Bool"#]]);
    }

    #[test]
    fn error_typecheck_ascription() {
        check_parse_error(
            "true as Nat",
            expect![[r#"[0-4]TypeError: Expected type `Nat`, got `Bool`"#]],
        );
        check_parse_error(
            "(λx:Bool.x) as Bool → Nat",
            expect![[r#"[0-12]TypeError: Expected type `Bool → Nat`, got `Bool → Bool`"#]],
        );
        check_parse_error(
            "λf:Bool → Bool.λb:Bool.(f as Bool → Nat) b",
            expect![[r#"[4-17]TypeError: Expected type `Bool → Nat`, got `Bool → Bool`"#]],
        );
        check_parse_error(
            "(λf:Bool → Bool.λb:Bool.f b) as Bool → Bool → Bool",
            expect![[
                r#"[0-32]TypeError: Expected type `Bool → Bool → Bool`, got `(Bool → Bool) → Bool → Bool`"#
            ]],
        );
    }

    #[test]
    fn typecheck_let_bindings() {
        check("let x = true in x", expect![[r#"Bool"#]]);
        check(
            "let not = λb:Bool.if b then false else true in not true",
            expect![[r#"Bool"#]],
        );
        check(
            "let not = λb:Bool.if b then false else true in not",
            expect![[r#"Bool → Bool"#]],
        );
        check("let {x} = {0} in x", expect![[r#"Nat"#]]);
        check(
            "let {f=f, l=l} = {f=true,l=0} in {f=l, l=f}",
            expect![[r#"{f:Nat, l:Bool}"#]],
        );
    }

    #[test]
    fn error_typecheck_let_bindings() {
        check_parse_error(
            "let x = true in succ x",
            expect![[r#"[8-12]TypeError: Expected type `Nat`, got `Bool`"#]],
        );
        check_parse_error(
            "let not = λb:Bool.if b then false else true in not 0",
            expect![[r#"[52-53]TypeError: Expected type `Bool`, got `Nat`"#]],
        );
        check_parse_error(
            "let {x} = true in x",
            expect![[r#"[0-19]TypeError: Only records can be pattern matched"#]],
        );
        check_parse_error(
            "let {x} = {0, true} in x",
            expect![[r#"[14-18]TypeError: The keys `2` are not matched against"#]],
        );
        check_parse_error(
            "let {f=x} = {x=true} in x",
            expect![[r#"[0-25]TypeError: The key `f` does not exist in the record"#]],
        );
        check_parse_error(
            "let {x} = {} in x",
            expect![[r#"[0-17]TypeError: The key `1` does not exist in the record"#]],
        );
        check_parse_error(
            "let {x} = {0, 0, 0} in x",
            expect![[r#"[14-18]TypeError: The keys `2, 3` are not matched against"#]],
        );
    }

    #[test]
    fn typecheck_record() {
        check("{true, true}", expect![[r#"{Bool, Bool}"#]]);
        check(
            "{first=true, last=true}",
            expect![[r#"{first:Bool, last:Bool}"#]],
        );
        check("{0, unit}.2", expect![[r#"Unit"#]]);
        check("{0, unit}.1", expect![[r#"Nat"#]]);

        check(
            "(λrec:{x:Bool,y:Nat}.rec.x){x=true, y=0}",
            expect![[r#"Bool"#]],
        );
    }

    #[test]
    fn error_typecheck_record() {
        check_parse_error(
            "{0}.1 as Bool",
            expect![[r#"[1-2]TypeError: Expected type `Bool`, got `Nat`"#]],
        );
        check_parse_error(
            "{{unit}}.1.1 as Bool",
            expect![[r#"[2-6]TypeError: Expected type `Bool`, got `Unit`"#]],
        );
        check_parse_error(
            "{} as Bool",
            expect![[r#"[0-2]TypeError: Expected type `Bool`, got `{}`"#]],
        );
        check_parse_error(
            "{true}.0",
            expect![[r#"[0-8]TypeError: The element `0` does not exist on the record `{Bool}`"#]],
        );
    }

    #[test]
    fn typecheck_definitions() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        check_env("let x = true;", expect![[r#"Unit"#]], &mut env, &mut tyenv);
        expect![[r#"Some(Some(Ty { span: Span { lo: 8, hi: 12 }, kind: Bool }))"#]].assert_eq(
            &format!(
                "{:?}",
                env.get_db_index("x")
                    .map(|idx| env.get_type_from_index(idx))
            ),
        );
        check_env(
            "let {y, z} = {true, 0};",
            expect![[r#"Unit"#]],
            &mut env,
            &mut tyenv,
        );
        expect![[r#"Some(Some(Ty { span: Span { lo: 14, hi: 18 }, kind: Bool }))"#]].assert_eq(
            &format!(
                "{:?}",
                env.get_db_index("y")
                    .map(|idx| env.get_type_from_index(idx))
            ),
        );
        expect![[r#"Some(Some(Ty { span: Span { lo: 20, hi: 21 }, kind: Nat }))"#]].assert_eq(
            &format!(
                "{:?}",
                env.get_db_index("z")
                    .map(|idx| env.get_type_from_index(idx))
            ),
        );
        check_env(
            "let {f=w} = {f=λx:Bool.x};",
            expect![[r#"Unit"#]],
            &mut env,
            &mut tyenv,
        );
        expect![[r#"Some(Some(Ty { span: Span { lo: 15, hi: 25 }, kind: Abstraction(Ty { span: Span { lo: 19, hi: 23 }, kind: Bool }, Ty { span: Span { lo: 19, hi: 23 }, kind: Bool }) }))"#]].assert_eq(&format!(
            "{:?}",
            env.get_db_index("w").map(|idx| env.get_type_from_index(idx))
        ));
        check_env(
            "type UU = Unit → Unit;",
            expect![[r#"Unit"#]],
            &mut env,
            &mut tyenv,
        );
        check_env("(λu:Unit.u) as UU", expect![["UU"]], &mut env, &mut tyenv);

        check_parse_error_env(
            "let a = 3 as Bool;",
            expect![[r#"[8-9]TypeError: Expected type `Bool`, got `Nat`"#]],
            &mut env,
            &mut tyenv,
        );
        check_env("let a = 3;", expect![[r#"Unit"#]], &mut env, &mut tyenv);
    }

    #[test]
    fn error_typecheck_definitions() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        check_env("let x = true;", expect![[r#"Unit"#]], &mut env, &mut tyenv);
        check_parse_error_env(
            "(λx:Nat.x)x",
            expect![[r#"[11-12]TypeError: Expected type `Nat`, got `Bool`"#]],
            &mut env,
            &mut tyenv,
        );
        check_env(
            "type UU = Unit → Unit;",
            expect![[r#"Unit"#]],
            &mut env,
            &mut tyenv,
        );
        check_parse_error_env(
            "true as UU",
            expect![[r#"[0-4]TypeError: Expected type `UU`, got `Bool`"#]],
            &mut env,
            &mut tyenv,
        );
    }

    #[test]
    fn typecheck_variants() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        check_env(
            "type MaybeNat = <some:Nat, none:Unit>;",
            expect![[r#"Unit"#]],
            &mut env,
            &mut tyenv,
        );

        check_env(
            "<some=0> as MaybeNat",
            expect![[r#"MaybeNat"#]],
            &mut env,
            &mut tyenv,
        );
        check_env(
            "<none=unit> as MaybeNat",
            expect![[r#"MaybeNat"#]],
            &mut env,
            &mut tyenv,
        );
    }

    #[test]
    fn error_typecheck_variants() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        check_env(
            "type MaybeNat = <some:Nat, none:Unit>;",
            expect![[r#"Unit"#]],
            &mut env,
            &mut tyenv,
        );

        check_parse_error_env(
            "0 as MaybeNat",
            expect![[r#"[0-1]TypeError: Expected type `MaybeNat`, got `Nat`"#]],
            &mut env,
            &mut tyenv,
        );

        check_parse_error_env(
            "<some=0> as Nat",
            expect![[r#"[12-15]TypeError: Expected a variant type, got `Nat`"#]],
            &mut env,
            &mut tyenv,
        );

        check_parse_error_env(
            "<invalid=0> as MaybeNat",
            expect![[r#"[0-23]TypeError: The label `invalid` is not a variant of `MaybeNat`"#]],
            &mut env,
            &mut tyenv,
        );
    }

    #[test]
    fn typecheck_case_of() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        check_env(
            "type MaybeNat = <some:Nat, none:Unit>;",
            expect![[r#"Unit"#]],
            &mut env,
            &mut tyenv,
        );

        check_env(
            r#"case <some=0> as MaybeNat of
                          <some=x> => true
                          | <none=_> => false"#,
            expect![[r#"Bool"#]],
            &mut env,
            &mut tyenv,
        );

        check_env(
            r#"λn:MaybeNat.case n of
                                <some=x> => <some=succ x> as MaybeNat
                                | <none=u> => <none=u> as MaybeNat"#,
            expect![[r#"MaybeNat → MaybeNat"#]],
            &mut env,
            &mut tyenv,
        );

        check_env(
            r#"(λn:MaybeNat.case n of
                                <some=x> => <some=succ x> as MaybeNat
                                | <none=u> => <none=u> as MaybeNat)
                <none=unit> as MaybeNat"#,
            expect![[r#"MaybeNat"#]],
            &mut env,
            &mut tyenv,
        );
    }

    #[test]
    fn error_typecheck_case_of() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        check_env(
            "type MaybeNat = <some:Nat, none:Unit>;",
            expect![[r#"Unit"#]],
            &mut env,
            &mut tyenv,
        );

        check_parse_error_env(
            "case 0 of <some=_> => unit",
            expect![[r#"[5-6]TypeError: Expected a variant type, got `Nat`"#]],
            &mut env,
            &mut tyenv,
        );

        check_parse_error_env(
            "case <none=unit> as MaybeNat of <invalid=_> => unit",
            expect![[r#"[0-51]TypeError: The label `invalid` is not a variant of `MaybeNat`"#]],
            &mut env,
            &mut tyenv,
        );

        check_parse_error_env(
            "case <none=unit> as MaybeNat of <some=_> => unit",
            expect![[r#"[0-48]TypeError: The label `none` is not covered"#]],
            &mut env,
            &mut tyenv,
        );
    }

    #[test]
    fn typecheck_fix() {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();

        check_env(
            r#"let ff = λie:Nat → Bool.
                         λx:Nat.
                          if iszero x then true
                          else if iszero (pred x) then false
                          else ie (pred (pred x));"#,
            expect![[r#"Unit"#]],
            &mut env,
            &mut tyenv,
        );

        check_env(
            r#"let iseven = fix ff; iseven"#,
            expect![[r#"Nat → Bool"#]],
            &mut env,
            &mut tyenv,
        );
    }

    #[test]
    fn typecheck_letrec() {
        check(
            r#"letrec iseven: Nat → Bool =
                λx:Nat.
                    if iszero x then true
                    else if iszero (pred x) then false
                    else iseven (pred (pred x))
                in iseven 7"#,
            expect![[r#"Bool"#]],
        );
    }

    #[test]
    fn typecheck_list() {
        check("nil[Bool]", expect![["List Bool"]]);
        check("cons[Bool] true nil[Bool]", expect![["List Bool"]]);
        check("isnil[Nat] nil[Nat]", expect![["Bool"]]);
        check("head[Nat] nil[Nat]", expect![["Nat"]]);
        check("tail[Nat] nil[Nat]", expect![["List Nat"]]);
    }

    #[test]
    fn error_typecheck_list() {
        check_parse_error(
            "cons[Bool] 0 nil[Bool]",
            expect![[r#"[11-12]TypeError: Expected type `Bool`, got `Nat"#]],
        );
        check_parse_error(
            "cons[Bool] true true",
            expect![[r#"[16-20]TypeError: Expected type `List Bool`, got `Bool`"#]],
        );
        check_parse_error(
            "cons[Bool] true nil[Nat]",
            expect![[r#"[16-24]TypeError: Expected type `List Bool`, got `List Nat`"#]],
        );
        check_parse_error(
            "cons[Bool] true nil[Nat]",
            expect![[r#"[16-24]TypeError: Expected type `List Bool`, got `List Nat`"#]],
        );
        check_parse_error(
            "isnil[Bool] true",
            expect![[r#"[12-16]TypeError: Expected type `List Bool`, got `Bool"#]],
        );
        check_parse_error(
            "isnil[Bool] nil[Nat]",
            expect![[r#"[12-20]TypeError: Expected type `List Bool`, got `List Nat"#]],
        );
        check_parse_error(
            "(λl:List Bool.head[Bool]l)λl:List Nat.head[Nat] l",
            expect![[r#"[27-51]TypeError: Expected type `List Bool`, got `(List Nat) → Nat`"#]],
        );
    }
}
