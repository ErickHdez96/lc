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
        let parsed = self.parse_application_or_var(env)?;

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

    fn parse_term(&mut self, env: &Env) -> Result<LTerm> {
        match self.current() {
            TokenKind::Ident => self.parse_ident(env),
            TokenKind::Number => self.parse_number(env),
            TokenKind::Unit => {
                self.next();
                Ok(T![unit])
            }
            TokenKind::Succ | TokenKind::Pred | TokenKind::IsZero => {
                let t = self.next().kind;
                let term = self.parse_application_or_var(&env)?;
                Ok(match t {
                    TokenKind::Succ => T![succ term],
                    TokenKind::Pred => T![pred term],
                    _ => T![iszero term],
                })
            }
            TokenKind::Lambda => self.parse_abstraction(env),
            TokenKind::LParen => {
                self.bump();
                let term = self.parse_application_or_var(env)?;
                self.eat(TokenKind::RParen)?;
                Ok(term)
            }
            TokenKind::Eof => Err(error!("Expected a term, got `<eof>`"; self.next().span)),
            TokenKind::RParen
            | TokenKind::Error
            | TokenKind::Period
            | TokenKind::Whitespace
            | TokenKind::Then
            | TokenKind::Else
            | TokenKind::Colon
            | TokenKind::Arrow
            | TokenKind::Wildcard
            | TokenKind::As
            | TokenKind::In
            | TokenKind::Assign
            | TokenKind::RBrace
            | TokenKind::Comma => {
                let t = self.next();
                Err(error!("Expected a term, got `{}`", t; t.span))
            }
            TokenKind::True => {
                self.bump();
                Ok(T![true])
            }
            TokenKind::False => {
                self.bump();
                Ok(T![false])
            }
            TokenKind::If => {
                self.bump();
                let cond = self.parse_application_or_var(&env)?;
                self.eat(TokenKind::Then)?;
                let then = self.parse_application_or_var(&env)?;
                self.eat(TokenKind::Else)?;
                let else_b = self.parse_application_or_var(&env)?;
                Ok(T![if cond, then, else_b])
            }
            TokenKind::Let => {
                self.bump();
                let (x, _) = self.eat_ident(true)?;
                self.eat(TokenKind::Assign)?;
                let t1 = self.parse_application_or_var(&env)?;
                self.eat(TokenKind::In)?;
                let mut env = Env::with_parent(&env);
                env.insert_let_variable(x);
                let t2 = self.parse_application_or_var(&env)?;
                Ok(T![let x, t1, t2])
            }
            TokenKind::LBrace => {
                self.bump();
                let mut terms = Vec::new();
                let mut comma_consumed = true;

                while self.current().can_start_term() {
                    terms.push(self.parse_application_or_var(&env)?);
                    if self.current() != TokenKind::Comma {
                        comma_consumed = false;
                        break;
                    }
                    self.eat(TokenKind::Comma)?;
                    comma_consumed = true;
                }

                match self.current() {
                    TokenKind::RBrace => self.bump(),
                    k => {
                        return Err(
                            error!("Expected {} or `}}`, got `{}`", if comma_consumed { "a term" } else { "`,`" }, k; self.next().span),
                        )
                    }
                }

                Ok(Rc::new(Term::Tuple(terms)))
            }
        }
    }

    fn parse_application_or_var(&mut self, env: &Env) -> Result<LTerm> {
        let mut application_items = vec![];
        while self.current().can_start_term() {
            let term = self.parse_term(&env)?;
            let term = self.parse_post_term(term, &env)?;
            application_items.push(term);
        }

        if application_items.is_empty() {
            let t = self.next();
            return Err(error!("Expected a term, got `{}`", t; t.span));
        }

        let mut application_items = application_items.into_iter();
        let t1 = application_items.next().unwrap();

        match application_items.next() {
            Some(t2) => {
                Ok(application_items.fold(T![app t1, t2], |acc, current| T![app acc, current]))
            }
            None => Ok(t1),
        }
    }

    fn parse_post_term(&mut self, mut t: LTerm, env: &Env) -> Result<LTerm> {
        loop {
            match self.current() {
                TokenKind::Period => {
                    self.bump();
                    let elem = self.eat_number()?;
                    t = T![proj t, elem];
                }
                TokenKind::As => {
                    self.bump();
                    let ty = self.parse_type(env)?;
                    t = T![asc t, ty];
                }
                _ => break,
            }
        }
        Ok(t)
    }

    fn eat_number(&mut self) -> Result<usize> {
        match self.current() {
            TokenKind::Number => {
                let t = self.next();
                t.text
                    .parse::<usize>()
                    .map_err(|_| error!("Number too large"; t.span))
            }
            k => Err(error!("Expected a number, got `{}`", k; self.next().span)),
        }
    }

    fn parse_number(&mut self, _env: &Env) -> Result<LTerm> {
        let n = self.eat_number()?;

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
        let body = self.parse_application_or_var(&env)?;
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
            TokenKind::LBrace => {
                self.bump();
                let mut types = Vec::new();
                let mut comma_consumed = true;

                while self.current().can_start_term() {
                    types.push(self.parse_type(&env)?);
                    if self.current() != TokenKind::Comma {
                        comma_consumed = false;
                        break;
                    }
                    self.eat(TokenKind::Comma)?;
                    comma_consumed = true;
                }

                match self.current() {
                    TokenKind::RBrace => self.bump(),
                    k => {
                        return Err(
                            error!("Expected {} or `}}`, got `{}`", if comma_consumed { "a type" } else { "`,`" }, k; self.next().span),
                        )
                    }
                }

                Rc::new(Ty::Tuple(types))
            }
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

    #[test]
    fn test_parse_ascription() {
        check("true as Bool", T![asc T![true], TY![bool]]);
        // Correct precedence
        check("succ 0 as Nat", T![succ T![asc T![0], TY![nat]]]);
        check("(succ 0) as Nat", T![asc T![succ T![0]], TY![nat]]);
        check(
            "λx:Bool.x as Bool",
            T![abs "x", TY![bool], T![asc T![var 0], TY![bool]]],
        );
        check(
            "(λx:Bool.x) as Bool → Bool",
            T![asc T![abs "x", TY![bool], T![var 0]], TY![abs TY![bool], TY![bool]]],
        );
    }

    #[test]
    fn error_parse_ascription() {
        check_error("true as", "Expected a type, got `<eof>`");
    }

    #[test]
    fn test_parse_let_bindings() {
        check("let x = true in x", T![let "x", T![true], T![var 0]]);
        check(
            "let not = λb:Bool.if b then false else true in not true",
            T![let "not", T![abs "b", TY![bool], T![if T![var 0], T![false], T![true]]], T![app T![var 0], T![true]]],
        );
        check(
            "let x = let y = false in y in x",
            T![let "x", T![let "y", T![false], T![var 0]], T![var 0]],
        );
    }

    #[test]
    fn error_parse_let_bindings() {
        check_error("let x = x in x", "Variable `x` not bound");
    }

    #[test]
    fn test_parse_tuple() {
        check("{}", T![tuple]);
        check("{true}", T![tuple T![true]]);
        check(
            "{λ_:Bool.true, λ_:Bool.false}",
            T![tuple T![abs "_", TY![bool], T![true]], T![abs "_", TY![bool], T![false]]],
        );
        check(
            "{(λb:Bool.b) true}",
            T![tuple T![app T![abs "b", TY![bool], T![var 0]], T![true]]],
        );
        check("{true, false}", T![tuple T![true], T![false]]);
        check("{succ 0}", T![tuple T![succ T![0]]]);
        check(
            "{0, 1, 2}",
            T![tuple T![0], T![succ T![0]], T![succ T![succ T![0]]]],
        );
        check(
            "{{unit, unit}, {unit}}",
            T![tuple T![tuple T![unit], T![unit]], T![tuple T![unit]]],
        );
        // We accept trailing commas
        check("{0,}", T![tuple T![0]]);

        check(
            "λt:{Bool, Bool}.t",
            T![abs "t", TY![tuple TY![bool], TY![bool]], T![var 0]],
        );
        check(
            "λt:{{Unit, Unit}, Bool}.t",
            T![abs "t", TY![tuple TY![tuple TY![unit], TY![unit]], TY![bool]], T![var 0]],
        );
        check("λt:{}.t", T![abs "t", TY![tuple], T![var 0]]);
    }

    #[test]
    fn error_parse_tuple() {
        check_error("{", "Expected a term or `}`, got `<eof>`");
        check_error("{true", "Expected `,` or `}`, got `<eof>`");
        check_error("{true,", "Expected a term or `}`, got `<eof>`");
        check_error("{true,,", "Expected a term or `}`, got `,`");
        check_error("{true ) true}", "Expected `,` or `}`, got `)`");
        check_error("λt:{", "Expected a type or `}`, got `<eof>`");
        check_error("λt:{Bool", "Expected `,` or `}`, got `<eof>`");
    }

    #[test]
    fn test_parse_tuple_projection() {
        check("{true}.1", T![proj T![tuple T![true]], 1]);
        check(
            "{} as {Bool, Bool}.1 as Bool",
            T![asc T![proj T![asc T![tuple], TY![tuple TY![bool], TY![bool]]], 1], TY![bool]],
        );
        check(
            "{true}.1 as Bool",
            T![asc T![proj T![tuple T![true]], 1], TY![bool]],
        );
        check(
            "{{true, unit}.1, 0}.2 as Nat",
            T![asc T![proj T![tuple T![proj T![tuple T![true], T![unit]], 1], T![0]], 2], TY![nat]],
        );
        check(
            "{{true, unit}.1, 0}.1.1",
            T![proj T![proj T![tuple T![proj T![tuple T![true], T![unit]], 1], T![0]], 1], 1],
        );
    }
}
