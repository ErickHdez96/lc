use crate::{Env, Error, ErrorKind, LTerm, Span, Symbol, TermKind, TY};
use std::{fmt, rc::Rc};

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
    Tuple(Vec<LTy>),
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
            Self::Tuple(elems) => {
                write!(
                    f,
                    "{{{}}}",
                    elems
                        .iter()
                        .map(ToString::to_string)
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
        TermKind::Let(x, ref t1, ref t2) => {
            let t1 = type_of(t1, &env)?;
            let mut env = Env::with_parent(&env);
            env.insert_local(x, t1);
            type_of(t2, &env)
        }
        TermKind::Tuple(ref elems) => elems
            .iter()
            .map(|e| type_of(e, &env))
            .collect::<Result<Vec<_>>>()
            .map(|elems| {
                Rc::new(Ty {
                    kind: TyKind::Tuple(elems),
                    span: type_t.span,
                })
            }),
        TermKind::Projection(ref tuple, elem_no) => {
            let tuple = type_of(tuple, &env)?;
            match tuple.as_ref().kind {
                TyKind::Tuple(ref elems) if elem_no > 0 => match elems.get(elem_no - 1) {
                    Some(elem) => Ok(elem.clone()),
                    None => Err(error!(
                        "The element `{}` does not exist on the tuple `{}`",
                        elem_no, tuple; type_t.span
                    )),
                },
                TyKind::Tuple(_) => Err(error!(
                    "Cannot access a tuple with `0`, projections start from `1`"; type_t.span
                )),
                _ => Err(error!("Only a tuple can be projected, got `{}`", tuple; tuple.span)),
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
    (tuple $($term:expr),*; $span:expr) => {
        Rc::new(Ty { kind: TyKind::Tuple(vec![$($term.clone()),*]), span: $span.into() })
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse, Term, S, T};

    const SPAN: Span = Span::new(0, 1);

    fn check_parse(input: &str, expected: LTy) {
        let env = Env::new();
        assert_eq!(
            type_of(&parse(input, &env).expect("Couldn't parse"), &env)
                .expect("Couldn't type check"),
            expected
        );
    }

    fn check_parse_error(input: &str, expected: &str) {
        let env = Env::new();
        assert_eq!(
            type_of(&parse(input, &env).expect("Couldn't parse"), &env)
                .expect_err("Shouldn't type check correctly")
                .to_string(),
            format!("TypeError: {}", expected),
        );
    }

    fn check(t: LTerm, expected: LTy) {
        let env = Env::new();
        assert_eq!(type_of(&t, &env).expect("Couldn't type check"), expected);
    }

    #[test]
    fn test_constant_types() {
        check(T![true; (0u32, 4u32)], TY![bool; S![0, 4]]);
    }

    #[test]
    fn test_types() {
        let bool_ty = TY![bool; SPAN];
        check_parse("λx:Bool.x", TY![abs bool_ty, bool_ty; SPAN]);
        // (Bool → Bool) → Bool → Bool
        check_parse(
            "λf:Bool→Bool.λb:Bool.f b",
            TY![abs TY![abs bool_ty, bool_ty; SPAN], TY![abs bool_ty, bool_ty; SPAN]; SPAN],
        );
    }

    #[test]
    fn test_if() {
        let bool_ty = TY![bool; SPAN];
        check_parse(
            "if (λx:Bool.x) true then λx:Bool.false else λx:Bool.x",
            TY![abs bool_ty, bool_ty; SPAN],
        );
    }

    #[test]
    fn test_wrong_application_types() {
        check_parse_error(
            "(λx:Bool.x)(λx:Bool.x)",
            "Expected type `Bool`, got `Bool → Bool`",
        );
        check_parse_error("true λx:Bool.x", "Expected an abstraction, got `Bool`");
        check_parse_error(
            "λf:Bool → Bool.λx:Bool.x f",
            "Expected an abstraction, got `Bool`",
        );
    }

    #[test]
    fn test_wrong_if_types() {
        check_parse_error(
            "if λx:Bool.x then true else false",
            "Guard conditional expects a Bool, got `Bool → Bool`",
        );
        check_parse_error(
            "if true then true else λx:Bool.x",
            "Arms of conditional have different types: `Bool`, and `Bool → Bool`",
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
        check_parse(
            "λx:A.x",
            TY![abs TY![base "A"; SPAN], TY![base "A"; SPAN]; SPAN],
        );
        check_parse(
            "λx:B.x",
            TY![abs TY![base "B"; SPAN], TY![base "B"; SPAN]; SPAN],
        );
        check_parse(
            "λf:A → A.λx:A. f(f(x))",
            TY![abs TY![abs TY![base "A"; SPAN], TY![base "A"; SPAN]; SPAN], TY![abs TY![base "A"; SPAN], TY![base "A"; SPAN]; SPAN]; SPAN],
        );
    }

    #[test]
    fn test_typecheck_nat() {
        check_parse("0", TY![nat; SPAN]);
        check_parse("5", TY![nat; SPAN]);
        check_parse("pred 0", TY![nat; SPAN]);
        check_parse("pred pred pred 0", TY![nat; SPAN]);
        check_parse("succ 0", TY![nat; SPAN]);
        check_parse("succ succ succ 0", TY![nat; SPAN]);
        check_parse("pred succ 0", TY![nat; SPAN]);
        check_parse("iszero 0", TY![bool; SPAN]);
        check_parse("iszero pred succ 0", TY![bool; SPAN]);

        // is_greater_than_one
        check_parse(
            "λx:Nat.iszero pred x",
            TY![abs TY![nat; SPAN], TY![bool; SPAN]; SPAN],
        );
        check_parse("(λx:Nat.iszero pred x) 0", TY![bool; SPAN]);
    }

    #[test]
    fn error_typecheck_nat() {
        check_parse_error("pred true", "Expected type `Nat`, got `Bool`");
        check_parse_error("succ true", "Expected type `Nat`, got `Bool`");
        check_parse_error(
            "succ succ succ pred succ true",
            "Expected type `Nat`, got `Bool`",
        );
        check_parse_error("iszero true", "Expected type `Nat`, got `Bool`");
        check_parse_error("pred iszero 0", "Expected type `Nat`, got `Bool`");
        check_parse_error("pred iszero true", "Expected type `Nat`, got `Bool`");
        check_parse_error(
            "if 0 then true else false",
            "Guard conditional expects a Bool, got `Nat`",
        );
        check_parse_error(
            "if iszero pred succ 0 then true else 0",
            "Arms of conditional have different types: `Bool`, and `Nat`",
        );
    }

    #[test]
    fn test_typecheck_unit() {
        check_parse("unit", TY![unit; SPAN]);
        check_parse("λx:Unit.x", TY![abs TY![unit; SPAN], TY![unit; SPAN]; SPAN]);
        check_parse(
            "λx:Nat.unit",
            TY![abs TY![nat; SPAN], TY![unit; SPAN]; SPAN],
        );
        check_parse("(λ_:Unit.unit)unit", TY![unit; SPAN]);
    }

    #[test]
    fn error_typecheck_unit() {
        check_parse_error("iszero unit", "Expected type `Nat`, got `Unit`");
        check_parse_error("(λx:Nat.unit) unit", "Expected type `Nat`, got `Unit`");
    }

    #[test]
    fn test_typecheck_ascription() {
        check_parse("true as Bool", TY![bool; SPAN]);
        check_parse("0 as Nat", TY![nat; SPAN]);
        check_parse(
            "(λx:Bool.x) as Bool → Bool",
            TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN],
        );
    }

    #[test]
    fn error_typecheck_ascription() {
        check_parse_error("true as Nat", "Expected type `Nat`, got `Bool`");
        check_parse_error(
            "(λx:Bool.x) as Bool → Nat",
            "Expected type `Bool → Nat`, got `Bool → Bool`",
        );
        check_parse_error(
            "λf:Bool → Bool.λb:Bool.(f as Bool → Nat) b",
            "Expected type `Bool → Nat`, got `Bool → Bool`",
        );
        check_parse_error(
            "(λf:Bool → Bool.λb:Bool.f b) as Bool → Bool → Bool",
            "Expected type `Bool → Bool → Bool`, got `(Bool → Bool) → Bool → Bool`",
        );
    }

    #[test]
    fn test_typecheck_let_bindings() {
        check_parse("let x = true in x", TY![bool; SPAN]);
        check_parse(
            "let not = λb:Bool.if b then false else true in not true",
            TY![bool; SPAN],
        );
        check_parse(
            "let not = λb:Bool.if b then false else true in not",
            TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN],
        );
    }

    #[test]
    fn error_typecheck_let_bindings() {
        check_parse_error("let x = true in succ x", "Expected type `Nat`, got `Bool`");
        check_parse_error(
            "let not = λb:Bool.if b then false else true in not 0",
            "Expected type `Bool`, got `Nat`",
        );
    }

    #[test]
    fn test_typecheck_tuple() {
        check_parse(
            "{true, true}",
            TY![tuple TY![bool; SPAN], TY![bool; SPAN]; SPAN],
        );
        check_parse("{0, unit}.2", TY![unit; SPAN]);
        check_parse("{0, unit}.1", TY![nat; SPAN]);
    }

    #[test]
    fn error_typecheck_tuple() {
        check_parse_error(
            "{true, 0} as {Bool, Bool}",
            "Expected type `{Bool, Bool}`, got `{Bool, Nat}`",
        );
        check_parse_error("{0}.1 as Bool", "Expected type `Bool`, got `Nat`");
        check_parse_error("{{unit}}.1.1 as Bool", "Expected type `Bool`, got `Unit`");
        check_parse_error("{} as Bool", "Expected type `Bool`, got `{}`");
        check_parse_error(
            "{true}.0",
            "Cannot access a tuple with `0`, projections start from `1`",
        );
    }
}
