use crate::{Env, LTerm, Term, TY};
use anyhow::{anyhow, Result};
use std::{fmt, rc::Rc};

pub type LTy = Rc<Ty>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Bool,
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
}
