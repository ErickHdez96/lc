use crate::{Env, LTerm, Symbol, Term, TY};
use anyhow::{anyhow, Result};
use std::{fmt, rc::Rc};

pub type LTy = Rc<Ty>;

/// ```text
/// T ::=
///     Bool    type of booleans
///     T → T   type of functions
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Nat,
    Base(Symbol),
    Abstraction(LTy, LTy),
}

impl Ty {
    pub fn is_abstraction(&self) -> bool {
        matches!(self, Ty::Abstraction(_, _))
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "Bool"),
            Self::Nat => write!(f, "Nat"),
            Self::Base(s) => s.fmt(f),
            Self::Abstraction(t1, t2) => {
                let (l_paren, r_paren) = if t1.is_abstraction() {
                    ("(", ")")
                } else {
                    ("", "")
                };
                write!(f, "{}{}{} → {}", l_paren, t1, r_paren, t2)
            }
        }
    }
}

pub fn type_of(t: &LTerm, env: &Env) -> Result<LTy> {
    match t.as_ref() {
        Term::True => Ok(TY![bool]),
        Term::False => Ok(TY![bool]),
        Term::Zero => Ok(TY![nat]),
        Term::Succ(t) | Term::Pred(t) => match type_of(t, &env)?.as_ref() {
            Ty::Nat => Ok(TY![nat]),
            t => Err(anyhow!("Expected type Nat, got `{}`", t)),
        },
        Term::IsZero(t) => match type_of(t, &env)?.as_ref() {
            Ty::Nat => Ok(TY![bool]),
            t => Err(anyhow!("Expected type Nat, got `{}`", t)),
        },
        Term::Abstraction(v, ty, body) => {
            let mut env = Env::with_parent(&env);
            env.insert_local(*v, ty.clone());
            type_of(body, &env).map(|body_ty| TY![abs ty, body_ty])
        }
        Term::Variable(idx) => env
            .get_type(*idx)
            .ok_or_else(|| anyhow!("Invalid de Bruijn index {}", idx)),
        Term::Application(t1, t2) => {
            let t1_ty = type_of(t1, &env)?;
            let t2_ty = type_of(t2, &env)?;

            match t1_ty.as_ref() {
                Ty::Abstraction(t11_ty, t12_ty) => {
                    if t11_ty == &t2_ty {
                        Ok(t12_ty.clone())
                    } else {
                        Err(anyhow!("Expected type `{}`, got `{}`", t11_ty, t2_ty))
                    }
                }
                _ => Err(anyhow!("Expected an abstraction, got `{}`", t1_ty)),
            }
        }
        Term::If(cond, then, else_b) => match type_of(cond, &env)?.as_ref() {
            Ty::Bool => {
                let then_ty = type_of(then, &env)?;
                let else_ty = type_of(else_b, &env)?;

                if then_ty == else_ty {
                    Ok(else_ty)
                } else {
                    Err(anyhow!(
                        "Arms of conditional have different types: `{}`, and `{}`",
                        then_ty,
                        else_ty
                    ))
                }
            }
            ty => Err(anyhow!("Guard conditional expects a Bool, got `{}`", ty)),
        },
    }
}

#[macro_export]
macro_rules! TY {
    (bool) => {
        Rc::new(Ty::Bool)
    };
    (nat) => {
        Rc::new(Ty::Nat)
    };
    (base $s:expr) => {
        Rc::new(Ty::Base($s.into()))
    };
    (abs $t1:expr, $t2:expr) => {
        Rc::new(Ty::Abstraction($t1.clone(), $t2.clone()))
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse, T};

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
                .expect_err("Couldn't type check")
                .to_string(),
            expected
        );
    }

    fn check(t: LTerm, expected: LTy) {
        let env = Env::new();
        assert_eq!(type_of(&t, &env).expect("Couldn't type check"), expected);
    }

    #[test]
    fn test_constant_types() {
        check(T![true], TY![bool]);
    }

    #[test]
    fn test_types() {
        let bool_ty = TY![bool];
        check_parse("λx:Bool.x", TY![abs bool_ty, bool_ty]);
        // (Bool → Bool) → Bool → Bool
        check_parse(
            "λf:Bool→Bool.λb:Bool.f b",
            TY![abs TY![abs bool_ty, bool_ty], TY![abs bool_ty, bool_ty]],
        );
    }

    #[test]
    fn test_if() {
        let bool_ty = TY![bool];
        check_parse(
            "if (λx:Bool.x) true then λx:Bool.false else λx:Bool.x",
            TY![abs bool_ty, bool_ty],
        );
    }

    #[test]
    fn test_wrong_application_types() -> Result<()> {
        let env = Env::new();
        let parsed = parse("(λx:Bool.x)(λx:Bool.x)", &env)?;
        assert_eq!(
            type_of(&parsed, &env)
                .expect_err("Expected a typechecking error")
                .to_string(),
            "Expected type `Bool`, got `Bool → Bool`",
        );

        let parsed = parse("true λx:Bool.x", &env)?;
        assert_eq!(
            type_of(&parsed, &env)
                .expect_err("Expected a typechecking error")
                .to_string(),
            "Expected an abstraction, got `Bool`",
        );

        let parsed = parse("λf:Bool → Bool.λx:Bool.x f", &env)?;
        assert_eq!(
            type_of(&parsed, &env)
                .expect_err("Expected a typechecking error")
                .to_string(),
            "Expected an abstraction, got `Bool`",
        );

        Ok(())
    }

    #[test]
    fn test_wrong_if_types() -> Result<()> {
        let env = Env::new();
        let parsed = parse("if λx:Bool.x then true else false", &env)?;
        assert_eq!(
            type_of(&parsed, &env)
                .expect_err("Expected a typechecking error")
                .to_string(),
            "Guard conditional expects a Bool, got `Bool → Bool`",
        );

        let parsed = parse("if true then true else λx:Bool.x", &env)?;
        assert_eq!(
            type_of(&parsed, &env)
                .expect_err("Expected a typechecking error")
                .to_string(),
            "Arms of conditional have different types: `Bool`, and `Bool → Bool`",
        );

        Ok(())
    }

    #[test]
    fn test_printing_correct_precedence() {
        let ty = TY![abs TY![bool], TY![abs TY![bool], TY![bool]]];
        // → is right associative
        assert_eq!(ty.to_string(), "Bool → Bool → Bool");

        let ty = TY![abs TY![abs TY![bool], TY![bool]], TY![bool]];
        assert_eq!(ty.to_string(), "(Bool → Bool) → Bool");
    }

    #[test]
    fn test_typecheck_base_types() -> Result<()> {
        let env = Env::new();

        let parsed = parse("λx:A.x", &env)?;
        assert_eq!(
            type_of(&parsed, &env).expect("Couldn't type check"),
            TY![abs TY![base "A"], TY![base "A"]],
        );

        let parsed = parse("λx:B.x", &env)?;
        assert_eq!(
            type_of(&parsed, &env).expect("Couldn't type check"),
            TY![abs TY![base "B"], TY![base "B"]],
        );

        let parsed = parse("λf:A → A.λx:A. f(f(x))", &env)?;
        assert_eq!(
            type_of(&parsed, &env).expect("Couldn't type check"),
            TY![abs TY![abs TY![base "A"], TY![base "A"]], TY![abs TY![base "A"], TY![base "A"]]],
        );

        Ok(())
    }

    #[test]
    fn test_typecheck_nat() -> Result<()> {
        check_parse("0", TY![nat]);
        check_parse("5", TY![nat]);
        check_parse("pred 0", TY![nat]);
        check_parse("pred pred pred 0", TY![nat]);
        check_parse("succ 0", TY![nat]);
        check_parse("succ succ succ 0", TY![nat]);
        check_parse("pred succ 0", TY![nat]);
        check_parse("iszero 0", TY![bool]);
        check_parse("iszero pred succ 0", TY![bool]);

        // is_greater_than_one
        check_parse("λx:Nat.iszero pred x", TY![abs TY![nat], TY![bool]]);
        check_parse("(λx:Nat.iszero pred x) 0", TY![bool]);

        Ok(())
    }

    #[test]
    fn error_typecheck_nat() -> Result<()> {
        check_parse_error("pred true", "Expected type Nat, got `Bool`");
        check_parse_error("succ true", "Expected type Nat, got `Bool`");
        check_parse_error(
            "succ succ succ pred succ true",
            "Expected type Nat, got `Bool`",
        );
        check_parse_error("iszero true", "Expected type Nat, got `Bool`");
        check_parse_error("pred iszero 0", "Expected type Nat, got `Bool`");
        check_parse_error("pred iszero true", "Expected type Nat, got `Bool`");
        check_parse_error(
            "if 0 then true else false",
            "Guard conditional expects a Bool, got `Nat`",
        );
        check_parse_error(
            "if iszero pred succ 0 then true else 0",
            "Arms of conditional have different types: `Bool`, and `Nat`",
        );

        Ok(())
    }
}