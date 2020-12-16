use crate::{Env, Error, ErrorKind, LTerm, Span, Symbol, TY, TermKind, term::Pattern};
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
#[derive(Debug, Clone, Eq)]
pub struct Ty {
    pub span: Span,
    pub kind: TyKind,
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyKind {
    Bool,
    Nat,
    Unit,
    Base(Symbol),
    Abstraction(LTy, LTy),
    Record(HashMap<Symbol, LTy>, /** Original order of the keys */ Vec<Symbol>),
}

pub type LTy = Rc<Ty>;

impl Ty {
    pub fn is_abstraction(&self) -> bool {
        matches!(self.kind, TyKind::Abstraction(_, _))
    }
}

impl TyKind {
    pub fn is_abstraction(&self) -> bool {
        matches!(self, TyKind::Abstraction(_, _))
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
            Self::Bool => write!(f, "Bool"),
            Self::Nat => write!(f, "Nat"),
            Self::Base(s) => s.fmt(f),
            Self::Unit => write!(f, "Unit"),
            Self::Abstraction(t1, t2) => {
                let (l_paren, r_paren) = if t1.is_abstraction() {
                    ("(", ")")
                } else {
                    ("", "")
                };
                write!(f, "{}{}{} → {}", l_paren, t1, r_paren, t2)
            }
            Self::Record(elems, keys) => {
                write!(
                    f,
                    "{{{}}}",
                    keys.iter().cloned()
                        .map(|k| format!("{}{}", symbol_to_record_key(k), elems.get(&k).unwrap()))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

pub fn type_of(type_t: &LTerm, env: &Env) -> Result<LTy> {
    match type_t.as_ref().kind {
        TermKind::True => Ok(TY![bool; type_t.span]),
        TermKind::False => Ok(TY![bool; type_t.span]),
        TermKind::Zero => Ok(TY![nat; type_t.span]),
        TermKind::Unit => Ok(TY![unit; type_t.span]),
        TermKind::Ascription(ref t, ref ty) => match type_of(t, &env)?.as_ref() {
            t if *t == **ty => Ok(ty.clone()),
            t => Err(error!("Expected type `{}`, got `{}`", ty, t; t.span)),
        },
        TermKind::Succ(ref t) | TermKind::Pred(ref t) => match &type_of(t, &env)?.as_ref() {
            t if t.kind == TyKind::Nat => Ok(TY![nat; type_t.span]),
            t => Err(error!("Expected type `Nat`, got `{}`", t; t.span)),
        },
        TermKind::IsZero(ref t) => match &type_of(t, &env)?.as_ref() {
            t if t.kind == TyKind::Nat => Ok(TY![bool; type_t.span]),
            t => Err(error!("Expected type `Nat`, got `{}`", t; t.span)),
        },
        TermKind::Abstraction(v, ref ty, ref body) => {
            let mut env = Env::with_parent(&env);
            env.insert_local(v, ty.clone());
            type_of(body, &env).map(|body_ty| TY![abs ty, body_ty; type_t.span])
        }
        TermKind::Variable(idx) => env
            .get_type(idx)
            .ok_or_else(|| error!("Invalid de Bruijn index {}", idx; type_t.span)),
        TermKind::Application(ref t1, ref t2) => {
            let t1_ty = type_of(t1, &env)?;
            let t2_ty = type_of(t2, &env)?;

            match t1_ty.as_ref().kind {
                TyKind::Abstraction(ref t11_ty, ref t12_ty) => {
                    if t11_ty == &t2_ty {
                        Ok(t12_ty.clone())
                    } else {
                        Err(error!("Expected type `{}`, got `{}`", t11_ty, t2_ty; t2.span))
                    }
                }
                _ => Err(error!("Expected an abstraction, got `{}`", t1_ty; t1.span)),
            }
        }
        TermKind::If(ref cond, ref then, ref else_b) => match &type_of(cond, &env)?.as_ref().kind {
            TyKind::Bool => {
                let then_ty = type_of(then, &env)?;
                let else_ty = type_of(else_b, &env)?;

                if then_ty == else_ty {
                    Ok(else_ty)
                } else {
                    Err(error!(
                        "Arms of conditional have different types: `{}`, and `{}`",
                        then_ty, else_ty; type_t.span
                    ))
                }
            }
            ty => Err(error!("Guard conditional expects a Bool, got `{}`", ty; cond.span)),
        },
        TermKind::Let(ref p, ref t1, ref t2) => {
            let t1 = type_of(t1, &env)?;
            let env = resolve_match(p, &t1, &env, type_t.span)?;
            type_of(t2, &env)
        }
        TermKind::Record(ref elems, ref keys) => keys
            .iter()
            .cloned()
            .map(|k| type_of(elems.get(&k).unwrap(), &env).map(|e| (k, e)))
            .collect::<Result<HashMap<_, _>>>()
            .map(|elems| {
                Rc::new(Ty {
                    kind: TyKind::Record(elems, keys.clone()),
                    span: type_t.span,
                })
            }),
        TermKind::Projection(ref record, elem) => {
            let record = type_of(record, &env)?;
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
    }
}

fn resolve_match<'a>(p: &Pattern, t: &LTy, env: &'a Env, p_span: Span) -> Result<Env<'a>> {
    let mut env = Env::with_parent(&env);
    inner_resolve_match(p, t, &mut env, p_span)?;
    return Ok(env);

    fn inner_resolve_match(p: &Pattern, t: &LTy, mut env: &mut Env, p_span: Span) -> Result<()> {
        match p {
            Pattern::Var(s) => match env.get_immediate(*s) {
                Some(_) => {
                    Err(error!("Binding `{}` already used", s; p_span))
                }
                _ => {
                    env.insert_local(*s, Rc::clone(t));
                    Ok(())
                }
            }
            Pattern::Record(recs, keys) => match t.as_ref().kind {
                TyKind::Record(ref trecs, ref tkeys) => {
                    if tkeys.len() > keys.len() {
                        let mut span_iter = tkeys[keys.len()..]
                            .iter()
                            .map(|k| trecs.get(&k).unwrap().span);
                        let start = span_iter.next().unwrap();
                        let p_span = span_iter
                            .fold(start, |acc, cur| acc.with_hi(cur.hi));
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
                                inner_resolve_match(recs.get(&key).unwrap(), trecs.get(&key).unwrap(), &mut env, p_span)?;
                            }
                            Some(_) if trecs.get(&key).is_some() => {
                                return Err(error!("Match keys must follow the same order as the record"; p_span));
                            }
                            _ => {
                                return Err(error!("The key `{}` does not exist in the record", key; p_span));
                            }
                        }
                    }

                    Ok(())
                }
                _ => Err(error!("Only records can be pattern matched"; p_span)),
            }
        }
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
        let env = Env::new();
        expected.assert_eq(&format!(
            "{}",
            &type_of(&parse(input, &env).expect("Couldn't parse"), &env)
                .expect("Couldn't evaluate")
        ));
    }

    fn check_parse_error(input: &str, expected: expect_test::Expect) {
        let env = Env::new();
        expected.assert_eq(
            &type_of(&parse(input, &env).expect("Couldn't parse"), &env)
                .expect_err("Shouldn't type check correctly")
                .to_string(),
        );
    }

    #[test]
    fn test_constant_types() {
        check("true", expect![[r#"Bool"#]]);
    }

    #[test]
    fn test_types() {
        check("λx:Bool.x", expect![[r#"Bool → Bool"#]]);
        // (Bool → Bool) → Bool → Bool
        check(
            "λf:Bool→Bool.λb:Bool.f b",
            expect![[r#"(Bool → Bool) → Bool → Bool"#]],
        );
    }

    #[test]
    fn test_if() {
        check(
            "if (λx:Bool.x) true then λx:Bool.false else λx:Bool.x",
            expect![[r#"Bool → Bool"#]],
        );
    }

    #[test]
    fn test_wrong_application_types() {
        check_parse_error(
            "(λx:Bool.x)(λx:Bool.x)",
            expect![["TypeError: Expected type `Bool`, got `Bool → Bool`"]],
        );
        check_parse_error(
            "true λx:Bool.x",
            expect![["TypeError: Expected an abstraction, got `Bool`"]],
        );
        check_parse_error(
            "λf:Bool → Bool.λx:Bool.x f",
            expect![["TypeError: Expected an abstraction, got `Bool`"]],
        );
    }

    #[test]
    fn test_wrong_if_types() {
        check_parse_error(
            "if λx:Bool.x then true else false",
            expect![["TypeError: Guard conditional expects a Bool, got `Bool → Bool`"]],
        );
        check_parse_error(
            "if true then true else λx:Bool.x",
            expect![[
                "TypeError: Arms of conditional have different types: `Bool`, and `Bool → Bool`"
            ]],
        );
    }

    #[test]
    fn test_printing_correct_precedence() {
        let ty = TY![abs TY![bool; SPAN], TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN]; SPAN];
        // → is right associative
        assert_eq!(ty.to_string(), "Bool → Bool → Bool");

        let ty = TY![abs TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN], TY![bool; SPAN]; SPAN];
        assert_eq!(ty.to_string(), "(Bool → Bool) → Bool");
    }

    #[test]
    fn test_typecheck_base_types() {
        check("λx:A.x", expect![[r#"A → A"#]]);
        check("λx:B.x", expect![[r#"B → B"#]]);
        check("λf:A → A.λx:A. f(f(x))", expect![[r#"(A → A) → A → A"#]]);
    }

    #[test]
    fn test_typecheck_nat() {
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
            expect![["TypeError: Expected type `Nat`, got `Bool`"]],
        );
        check_parse_error(
            "succ true",
            expect![["TypeError: Expected type `Nat`, got `Bool`"]],
        );
        check_parse_error(
            "succ succ succ pred succ true",
            expect![["TypeError: Expected type `Nat`, got `Bool`"]],
        );
        check_parse_error(
            "iszero true",
            expect![["TypeError: Expected type `Nat`, got `Bool`"]],
        );
        check_parse_error(
            "pred iszero 0",
            expect![["TypeError: Expected type `Nat`, got `Bool`"]],
        );
        check_parse_error(
            "pred iszero true",
            expect![["TypeError: Expected type `Nat`, got `Bool`"]],
        );
        check_parse_error(
            "if 0 then true else false",
            expect![["TypeError: Guard conditional expects a Bool, got `Nat`"]],
        );
        check_parse_error(
            "if iszero pred succ 0 then true else 0",
            expect![["TypeError: Arms of conditional have different types: `Bool`, and `Nat`"]],
        );
    }

    #[test]
    fn test_typecheck_unit() {
        check("unit", expect![[r#"Unit"#]]);
        check("λx:Unit.x", expect![[r#"Unit → Unit"#]]);
        check("λx:Nat.unit", expect![[r#"Nat → Unit"#]]);
        check("(λ_:Unit.unit)unit", expect![[r#"Unit"#]]);
    }

    #[test]
    fn error_typecheck_unit() {
        check_parse_error(
            "iszero unit",
            expect![["TypeError: Expected type `Nat`, got `Unit`"]],
        );
        check_parse_error(
            "(λx:Nat.unit) unit",
            expect![["TypeError: Expected type `Nat`, got `Unit`"]],
        );
    }

    #[test]
    fn test_typecheck_ascription() {
        check("true as Bool", expect![[r#"Bool"#]]);
        check("0 as Nat", expect![[r#"Nat"#]]);
        check("(λx:Bool.x) as Bool → Bool", expect![[r#"Bool → Bool"#]]);
    }

    #[test]
    fn error_typecheck_ascription() {
        check_parse_error(
            "true as Nat",
            expect![["TypeError: Expected type `Nat`, got `Bool`"]],
        );
        check_parse_error(
            "(λx:Bool.x) as Bool → Nat",
            expect![["TypeError: Expected type `Bool → Nat`, got `Bool → Bool`"]],
        );
        check_parse_error(
            "λf:Bool → Bool.λb:Bool.(f as Bool → Nat) b",
            expect![["TypeError: Expected type `Bool → Nat`, got `Bool → Bool`"]],
        );
        check_parse_error(
            "(λf:Bool → Bool.λb:Bool.f b) as Bool → Bool → Bool",
            expect![[
                "TypeError: Expected type `Bool → Bool → Bool`, got `(Bool → Bool) → Bool → Bool`"
            ]],
        );
    }

    #[test]
    fn test_typecheck_let_bindings() {
        check("let x = true in x", expect![[r#"Bool"#]]);
        check(
            "let not = λb:Bool.if b then false else true in not true",
            expect![[r#"Bool"#]],
        );
        check(
            "let not = λb:Bool.if b then false else true in not",
            expect![[r#"Bool → Bool"#]],
        );
        check(
            "let {x} = {0} in x",
            expect![[r#"Nat"#]],
        );
        check(
            "let {f=f, l=l} = {f=true,l=0} in {f=l, l=f}",
            expect![[r#"{f:Nat, l:Bool}"#]],
        );
    }

    #[test]
    fn error_typecheck_let_bindings() {
        //check_parse_error(
        //    "let x = true in succ x",
        //    expect![["TypeError: Expected type `Nat`, got `Bool`"]],
        //);
        //check_parse_error(
        //    "let not = λb:Bool.if b then false else true in not 0",
        //    expect![["TypeError: Expected type `Bool`, got `Nat`"]],
        //);
        //check_parse_error(
        //    "let {x} = true in x",
        //    expect![[r#"TypeError: Only records can be pattern matched"#]],
        //);
        //check_parse_error(
        //    "let {x} = {0, true} in x",
        //    expect![[r#"TypeError: The keys `2` are not matched against"#]],
        //);
        //check_parse_error(
        //    "let {f=x} = {x=true} in x",
        //    expect![[r#"TypeError: The key `f` does not exist in the record"#]],
        //);
        //check_parse_error(
        //    "let {x} = {} in x",
        //    expect![[r#"TypeError: The key `1` does not exist in the record"#]],
        //);
        check_parse_error(
            "let {x} = {0, 0, 0} in x",
            expect![[r#"TypeError: The keys `2, 3` are not matched against"#]],
        );
        //check_parse_error(
        //    "let {x,x} = {0, 0} in x",
        //    expect![[r#"TypeError: Binding `x` already used"#]],
        //);
        //check_parse_error(
        //    "let {f=x,l=x} = {f=true, l=false} in x",
        //    expect![[r#"TypeError: Binding `x` already used"#]],
        //);
    }

    #[test]
    fn test_typecheck_record() {
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
            expect![[r#"TypeError: Expected type `Bool`, got `Nat`"#]],
        );
        check_parse_error(
            "{{unit}}.1.1 as Bool",
            expect![[r#"TypeError: Expected type `Bool`, got `Unit`"#]],
        );
        check_parse_error(
            "{} as Bool",
            expect![["TypeError: Expected type `Bool`, got `{}`"]],
        );
        check_parse_error(
            "{true}.0",
            expect![[r#"TypeError: The element `0` does not exist on the record `{Bool}`"#]],
        );
    }
}
