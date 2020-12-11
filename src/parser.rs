use crate::Env;
use crate::{
    lexer::{tokenize, Token, TokenKind},
    Symbol, T,
};
use crate::{
    term::{LTerm, Term},
    Error, ErrorKind, TY,
};
use crate::{
    types::{LTy, Ty},
    Span,
};
use std::rc::Rc;

type Result<T> = std::result::Result<T, Error>;

macro_rules! error {
    ($msg:expr, $($arg:expr),*; $span:expr) => {
        Error::new(format!($msg, $($arg),*), $span, ErrorKind::Parser)
    };
    ($msg:expr; $span:expr) => {
        error!($msg,;$span)
    };
}

pub fn parse(input: &str, env: &Env<'static>) -> Result<LTerm> {
    let tokens = tokenize(input);
    let parser = Parser::new(&tokens);
    parser.parse(env)
}

#[derive(Debug)]
struct Parser<'a> {
    tokens: &'a [Token<'a>],
    cursor: usize,
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token<'a>]) -> Self {
        Self { tokens, cursor: 0 }
    }

    fn parse(mut self, env: &Env) -> Result<LTerm> {
        let parsed = self.parse_term(true, env)?;

        match self.next() {
            t if t.kind != TokenKind::Eof => Err(error!("Expected <eof>, got `{}`", t; t.span)),
            _ => Ok(parsed),
        }
    }

    fn current(&self) -> TokenKind {
        self.nth(0)
    }

    fn nth(&self, n: usize) -> TokenKind {
        self.tokens
            .get(self.cursor + n)
            .map(|t| t.kind)
            .unwrap_or_default()
    }

    fn next(&mut self) -> Token {
        let t = self.tokens.get(self.cursor).copied().unwrap_or_default();
        self.cursor += 1;
        t
    }

    fn bump(&mut self) {
        self.cursor += 1;
    }

    fn eat(&mut self, kind: TokenKind) -> Result<Token> {
        if self.current() == kind {
            Ok(self.next())
        } else {
            let t = self.next();
            Err(error!("Expected a `{}`, got `{}`", kind, t.kind; t.span))
        }
    }

    fn parse_term(&mut self, parse_application: bool, env: &Env) -> Result<LTerm> {
        match self.current() {
            TokenKind::Ident if !parse_application => self.parse_ident(env),
            TokenKind::Number if !parse_application => self.parse_number(env),
            TokenKind::Unit if !parse_application => {
                self.next();
                Ok(T![unit])
            }
            TokenKind::Succ | TokenKind::Pred | TokenKind::IsZero if !parse_application => {
                let t = self.next().kind;
                let term = self.parse_term(false, &env)?;
                Ok(match t {
                    TokenKind::Succ => T![succ term],
                    TokenKind::Pred => T![pred term],
                    _ => T![iszero term],
                })
            }
            TokenKind::Lambda => self.parse_abstraction(env),
            TokenKind::LParen if !parse_application => {
                self.bump();
                let term = self.parse_term(true, env)?;
                self.eat(TokenKind::RParen)?;
                Ok(term)
            }
            TokenKind::LParen => self.parse_application_or_var(env),
            TokenKind::Eof => Err(error!("Expected a term, got `<eof>`"; self.next().span)),
            TokenKind::RParen
            | TokenKind::Error
            | TokenKind::Period
            | TokenKind::Whitespace
            | TokenKind::Then
            | TokenKind::Else
            | TokenKind::Colon
            | TokenKind::Arrow
            | TokenKind::Wildcard => {
                let t = self.next();
                Err(error!("Expected a term, got `{}`", t; t.span))
            }
            TokenKind::True if !parse_application => {
                self.bump();
                Ok(T![true])
            }
            TokenKind::False if !parse_application => {
                self.bump();
                Ok(T![false])
            }
            TokenKind::If => {
                self.bump();
                let cond = self.parse_term(true, &env)?;
                self.eat(TokenKind::Then)?;
                let then = self.parse_term(true, &env)?;
                self.eat(TokenKind::Else)?;
                let else_b = self.parse_term(true, &env)?;
                Ok(T![if cond, then, else_b])
            }
            TokenKind::Ident
            | TokenKind::True
            | TokenKind::False
            | TokenKind::Succ
            | TokenKind::Pred
            | TokenKind::IsZero
            | TokenKind::Unit
            | TokenKind::Number => self.parse_application_or_var(env),
        }
    }

    fn parse_application_or_var(&mut self, env: &Env) -> Result<LTerm> {
        let mut application_items = vec![];
        while self.current().can_start_term() {
            let term = self.parse_term(false, &env)?;
            application_items.push(term);
        }
        debug_assert!(
            !application_items.is_empty(),
            "At least one term should have been parsed"
        );

        let mut application_items = application_items.into_iter();
        let t1 = application_items.next().unwrap();

        match application_items.next() {
            Some(t2) => {
                Ok(application_items.fold(T![app t1, t2], |acc, current| T![app acc, current]))
            }
            None => Ok(t1),
        }
    }

    fn parse_number(&mut self, _env: &Env) -> Result<LTerm> {
        let t = self.next();
        let n = t
            .text
            .parse::<u64>()
            .map_err(|_| error!("Number too large"; t.span))?;

        let mut number = T![0];
        for _ in 0..n {
            number = T![succ number];
        }
        Ok(number)
    }

    fn parse_ident(&mut self, env: &Env) -> Result<LTerm> {
        debug_assert_eq!(
            self.current(),
            TokenKind::Ident,
            "parse_ident expects to be called on an identifier"
        );
        let (s, span) = self.eat_ident(false)?;
        Ok(T![var self.lookup_ident(s, env).map_err(|e| error!("{}", e; span))?])
    }

    fn lookup_ident(&self, s: Symbol, env: &Env) -> std::result::Result<usize, String> {
        env.get_db_index(s)
            .ok_or_else(|| format!("Variable `{}` not bound", s))
    }

    fn eat_ident(&mut self, accept_wildcard: bool) -> Result<(Symbol, Span)> {
        match self.current() {
            TokenKind::Wildcard if accept_wildcard => {
                let t = self.next();
                Ok((Symbol::from(t.text), t.span))
            }
            TokenKind::Ident => {
                let t = self.next();
                Ok((Symbol::from(t.text), t.span))
            }
            _ => {
                let t = self.next();
                Err(error!("Expected an identifier, got `{}`", t; t.span))
            }
        }
    }

    fn parse_abstraction(&mut self, env: &Env) -> Result<LTerm> {
        self.bump();
        let (ident, _) = self.eat_ident(true)?;
        self.eat(TokenKind::Colon)?;
        let ty = self.parse_type(&env)?;
        self.eat(TokenKind::Period)?;
        let mut env = Env::with_parent(env);
        env.insert_local(ident, ty.clone());
        let body = self.parse_term(true, &env)?;
        Ok(T![abs ident, ty, body])
    }

    fn parse_type(&mut self, env: &Env) -> Result<LTy> {
        let ty = match self.current() {
            TokenKind::LParen => {
                self.bump();
                let ty = self.parse_type(&env)?;
                self.eat(TokenKind::RParen)?;
                ty
            }
            TokenKind::Ident => match self.next().text {
                "Bool" => Rc::new(Ty::Bool),
                "Nat" => Rc::new(Ty::Nat),
                "Unit" => Rc::new(Ty::Unit),
                text => Rc::new(Ty::Base(text.into())),
            },
            _ => {
                let t = self.next();
                return Err(error!("Expected a type, got `{}`", t; t.span));
            }
        };

        if self.current() == TokenKind::Arrow {
            self.bump();
            Ok(TY![abs ty, self.parse_type(&env)?])
        } else {
            Ok(ty)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{env::base_env, T, TY};
    use std::rc::Rc;

    fn check(input: &str, expected: LTerm) {
        assert_eq!(
            parse(input, &Env::new()).expect("Could not parse"),
            expected
        );
    }

    fn check_error(input: &str, expected: &str) {
        assert_eq!(
            parse(input, &Env::new())
                .expect_err("Shouldn't parse correctly")
                .to_string(),
            format!("ParserError: {}", expected),
        );
    }

    #[test]
    fn test_parse_variable() -> Result<()> {
        let mut env = Env::new();
        let id = parse("λx:Bool.x", &env)?;
        env.insert_variable("id", id, TY![abs TY![bool], TY![bool]]);
        assert_eq!(parse("id", &env)?, T![var 0]);
        Ok(())
    }

    #[test]
    fn test_parse_abstraction() {
        check("λx:Bool.x", T![abs "x", TY![bool], T![var 0]]);
        check(r"\x:Bool.x", T![abs "x", TY![bool], T![var 0]]);
        check(
            r"λx:Bool.λ_:Bool.x",
            T![abs "x", TY![bool], T![abs "_", TY![bool], T![var 1]]],
        );
    }

    #[test]
    fn test_parse_application() {
        let x = T![var 0];
        check("λx:Bool.x x", T![abs "x", TY![bool], T![app x, x]]);
    }

    #[test]
    fn test_parse_parenthesis() {
        let x = T![var 0];
        let y = T![var 0];
        check(
            "λy:Bool.(λx:Bool.x) y",
            T![abs "y", TY![bool], T![app T![abs "x", TY![bool], x], y]],
        );
    }

    #[test]
    fn error_parse_abstraction_no_body() {
        check_error("λx:Bool.", "Expected a term, got `<eof>`");
        check_error("λx", "Expected a `:`, got `<eof>`");
        check_error("λ", "Expected an identifier, got `<eof>`");
    }

    #[test]
    fn error_parse_unmatched_parens() {
        check_error("(", "Expected a term, got `<eof>`");
        check_error("(λx:Bool.x", "Expected a `)`, got `<eof>`");
        check_error(")", "Expected a term, got `)`");
    }

    #[test]
    fn error_parse_unknown_character() {
        check_error(";", "Expected a term, got `;`");
    }

    /// A single term inside parentheses should parse to the term inside.
    #[test]
    fn test_parse_single_term_inside_parentheses() -> Result<()> {
        let env = base_env();
        assert_eq!(parse("(λx:Bool.x)", &env)?, parse("λx:Bool.x", &env)?);
        Ok(())
    }

    #[test]
    fn test_pparse_aren_type() {
        check("λx:(Bool).x", T![abs "x", TY![bool], T![var 0]]);
    }

    #[test]
    fn test_parse_arrow_types() {
        // Bool → Bool
        let b_b_ty = TY![abs TY![bool], TY![bool]];
        check(
            "λf:Bool → Bool.λb:Bool.f b",
            T![abs "f", b_b_ty, T![abs "b", TY![bool], T![app T![var 1], T![var 0]]]],
        );

        // arrow is right associative
        // Bool → Bool → Bool = Bool → (Bool → Bool)
        let b_b_b_ty = TY![abs TY![bool], b_b_ty];
        check(
            "λf:Bool → Bool → Bool.λb1:Bool.λb2:Bool.f b1 b2",
            T![abs "f", b_b_b_ty, T![abs "b1", TY![bool], T![abs "b2", TY![bool], T![app T![app T![var 2], T![var 1]], T![var 0]]]]],
        );

        let b_b_b_ty_2 = TY![abs b_b_ty, TY![bool]];
        check(
            "λf:(Bool → Bool) → Bool.λb:Bool → Bool.f b",
            T![abs "f", b_b_b_ty_2, T![abs "b", TY![abs TY![bool], TY![bool]], T![app T![var 1], T![var 0]]]],
        );
    }

    #[test]
    fn test_parse_if() -> Result<()> {
        let env = Env::new();
        let bool_id = parse("λx:Bool.x", &env)?;

        check(
            "if
                (λx:Bool.x) true
            then
                λx:Bool.x
            else
                λx:Bool.false",
            T![
                if
                T![app bool_id, T![true]],
                bool_id,
                T![abs "x", TY![bool], T![false]],
            ],
        );

        Ok(())
    }

    #[test]
    fn test_parse_base_type() {
        check("λx:A.x", T![abs "x", TY![base "A"], T![var 0]]);
        check(
            "λx:A → A.x",
            T![abs "x", TY![abs TY![base "A"], TY![base "A"]], T![var 0]],
        );
    }

    #[test]
    fn test_parse_nats() {
        check("0", T![0]);
        check("1", T![succ T![0]]);
        check("5", T![succ T![succ T![succ T![succ T![succ T![0]]]]]]);
        // We parse it, but the typechecker throws an error
        check("0 0", T![app T![0], T![0]]);
        check("λx:Nat.x", T![abs "x", TY![nat], T![var 0]]);
        check("pred 0", T![pred T![0]]);
        check("pred true", T![pred T![true]]);
        check("succ 0", T![succ T![0]]);
        check("iszero 0", T![iszero T![0]]);
        check("iszero pred 0", T![iszero T![pred T![0]]]);
        check(
            "if iszero pred 0 then false else true",
            T![if T![iszero T![pred T![0]]], T![false], T![true]],
        );
    }

    #[test]
    fn test_parse_unit() {
        check("unit", T![unit]);
        check("λx:Nat.unit", T![abs "x", TY![nat], T![unit]]);
        check("λx:Unit.x", T![abs "x", TY![unit], T![var 0]]);
    }
}
