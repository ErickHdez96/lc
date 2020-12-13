use crate::{
    lexer::{tokenize, Token, TokenKind},
    Symbol, T,
};
use crate::{
    term::{LTerm, Term, TermKind},
    Error, ErrorKind, TY,
};
use crate::{types::Ty, Env};
use crate::{
    types::{LTy, TyKind},
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

    fn current_span(&self) -> Span {
        self.tokens
            .get(self.cursor)
            .map(|t| t.span)
            .unwrap_or_else(|| {
                self.tokens
                    .iter()
                    .last()
                    .map(|t| t.span)
                    .unwrap_or_else(|| Span::new(0, 1))
            })
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
                let span = self.next().span;
                Ok(T![unit; span])
            }
            TokenKind::Succ | TokenKind::Pred | TokenKind::IsZero => {
                let span = self.current_span();
                let t = self.next().kind;
                let term = self.parse_application_or_var(&env)?;
                let span = span.with_hi(term.span.hi);
                Ok(match t {
                    TokenKind::Succ => T![succ term; span],
                    TokenKind::Pred => T![pred term; span],
                    _ => T![iszero term; span],
                })
            }
            TokenKind::Lambda => self.parse_abstraction(env),
            TokenKind::LParen => {
                let span = self.current_span();
                self.bump();
                let mut term = self.parse_application_or_var(env)?;
                let span = span.with_hi(self.eat(TokenKind::RParen)?.span.hi);
                if let Some(t) = Rc::get_mut(&mut term) {
                    t.span = span;
                }
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
                let span = self.current_span();
                self.bump();
                Ok(T![true; span])
            }
            TokenKind::False => {
                let span = self.current_span();
                self.bump();
                Ok(T![false; span])
            }
            TokenKind::If => {
                let span = self.current_span();
                self.bump();
                let cond = self.parse_application_or_var(&env)?;
                self.eat(TokenKind::Then)?;
                let then = self.parse_application_or_var(&env)?;
                self.eat(TokenKind::Else)?;
                let else_b = self.parse_application_or_var(&env)?;
                let span = span.with_hi(else_b.span.hi);
                Ok(T![if cond, then, else_b; span])
            }
            TokenKind::Let => {
                let span = self.current_span();
                self.bump();
                let (x, _) = self.eat_ident(true)?;
                self.eat(TokenKind::Assign)?;
                let t1 = self.parse_application_or_var(&env)?;
                self.eat(TokenKind::In)?;
                let mut env = Env::with_parent(&env);
                env.insert_let_variable(x);
                let t2 = self.parse_application_or_var(&env)?;
                let span = span.with_hi(t2.span.hi);
                Ok(T![let x, t1, t2; span])
            }
            TokenKind::LBrace => {
                let span = self.current_span();
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

                let brace_span = match self.current() {
                    TokenKind::RBrace => self.next().span,
                    k => {
                        return Err(
                            error!("Expected {} or `}}`, got `{}`", if comma_consumed { "a term" } else { "`,`" }, k; self.next().span),
                        )
                    }
                };

                let span = span.with_hi(brace_span.hi);
                Ok(Rc::new(Term {
                    kind: TermKind::Tuple(terms),
                    span,
                }))
            }
        }
    }

    fn parse_application_or_var(&mut self, env: &Env) -> Result<LTerm> {
        let span = self.current_span();
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
                let mut c_span = span.with_hi(t2.span.hi);
                Ok(
                    application_items.fold(T![app t1, t2; c_span], move |acc, current| {
                        c_span = c_span.with_hi(current.span.hi);
                        T![app acc, current; c_span]
                    }),
                )
            }
            None => Ok(t1),
        }
    }

    fn parse_post_term(&mut self, mut t: LTerm, env: &Env) -> Result<LTerm> {
        loop {
            match self.current() {
                TokenKind::Period => {
                    self.bump();
                    let (elem, end) = self.eat_number()?;
                    let span = t.span.with_hi(end.hi);
                    t = T![proj t, elem; span];
                }
                TokenKind::As => {
                    self.bump();
                    let ty = self.parse_type(env)?;
                    let span = t.span.with_hi(self.current_span().hi);
                    t = T![asc t, ty; span];
                }
                _ => break,
            }
        }
        Ok(t)
    }

    fn eat_number(&mut self) -> Result<(usize, Span)> {
        match self.current() {
            TokenKind::Number => {
                let t = self.next();
                t.text
                    .parse::<usize>()
                    .map(|n| (n, t.span))
                    .map_err(|_| error!("Number too large"; t.span))
            }
            k => Err(error!("Expected a number, got `{}`", k; self.next().span)),
        }
    }

    fn parse_number(&mut self, _env: &Env) -> Result<LTerm> {
        let (n, span) = self.eat_number()?;

        let mut number = T![0; span];
        for _ in 0..n {
            number = T![succ number; span];
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
        Ok(T![var self.lookup_ident(s, env).map_err(|e| error!("{}", e; span))?; span])
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
        let span = self.current_span();
        self.bump();
        let (ident, _) = self.eat_ident(true)?;
        self.eat(TokenKind::Colon)?;
        let ty = self.parse_type(&env)?;
        self.eat(TokenKind::Period)?;
        let mut env = Env::with_parent(env);
        env.insert_local(ident, ty.clone());
        let body = self.parse_application_or_var(&env)?;
        let span = span.with_hi(body.span.hi);
        Ok(T![abs ident, ty, body; span])
    }

    fn parse_type(&mut self, env: &Env) -> Result<LTy> {
        let ty = match self.current() {
            TokenKind::LParen => {
                self.bump();
                let ty = self.parse_type(&env)?;
                self.eat(TokenKind::RParen)?;
                ty
            }
            TokenKind::Ident => match self.next() {
                t if t.text == "Bool" => Rc::new(Ty {
                    kind: TyKind::Bool,
                    span: t.span,
                }),
                t if t.text == "Nat" => Rc::new(Ty {
                    kind: TyKind::Nat,
                    span: t.span,
                }),
                t if t.text == "Unit" => Rc::new(Ty {
                    kind: TyKind::Unit,
                    span: t.span,
                }),
                t => Rc::new(Ty {
                    kind: TyKind::Base(t.text.into()),
                    span: t.span,
                }),
            },
            TokenKind::LBrace => {
                let span = self.current_span();
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

                let brace_span = match self.current() {
                    TokenKind::RBrace => self.next().span,
                    k => {
                        return Err(
                            error!("Expected {} or `}}`, got `{}`", if comma_consumed { "a type" } else { "`,`" }, k; self.next().span),
                        )
                    }
                };

                let span = span.with_hi(brace_span.hi);
                Rc::new(Ty {
                    kind: TyKind::Tuple(types),
                    span,
                })
            }
            _ => {
                let t = self.next();
                return Err(error!("Expected a type, got `{}`", t; t.span));
            }
        };

        if self.current() == TokenKind::Arrow {
            self.bump();
            let rh_ty = self.parse_type(&env)?;
            Ok(TY![abs ty, rh_ty; ty.span.with_hi(rh_ty.span.hi)])
        } else {
            Ok(ty)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{env::base_env, S, T, TY};
    use std::rc::Rc;

    const SPAN: Span = Span::new(0, 0);

    fn check(input: &str, expected: LTerm) {
        assert_eq!(
            parse(input, &Env::new()).expect("Could not parse").kind,
            expected.kind,
        );
    }

    fn check_error(input: &str, expected: &str) {
        assert_eq!(
            parse(input, &Env::new())
                .expect_err("Shouldn't parse correctly")
                .to_string(),
            format!("SyntaxError: {}", expected),
        );
    }

    #[test]
    fn test_parse_variable() -> Result<()> {
        let mut env = Env::new();
        let id = parse("λx:Bool.x", &env)?;
        env.insert_variable("id", id, TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN]);
        assert_eq!(parse("id", &env)?, T![var 0; S![0, 2]]);
        Ok(())
    }

    #[test]
    fn test_parse_abstraction() {
        check(
            "λx:Bool.x",
            T![abs "x", TY![bool; SPAN], T![var 0; S![9, 10]]; S![0, 10]],
        );
        check(
            r"\x:Bool.x",
            T![abs "x", TY![bool; SPAN], T![var 0; S![8, 9]]; S![0, 9]],
        );
        check(
            r"λx:Bool.λ_:Bool.x",
            T![abs "x", TY![bool; SPAN], T![abs "_", TY![bool; SPAN], T![var 1; S![18, 19]]; S![9, 19]]; S![0, 19]],
        );
    }

    #[test]
    fn test_parse_application() {
        check(
            "λx:Bool.x x",
            T![abs "x", TY![bool; SPAN], T![app T![var 0; S![9, 10]], T![var 0; S![11, 12]]; S![9, 12]]; S![0, 12]],
        );
    }

    #[test]
    fn test_parse_parenthesis() {
        let x = T![var 0; S![19, 20]];
        let y = T![var 0; S![22, 23]];
        check(
            "λy:Bool.(λx:Bool.x) y",
            T![abs "y", TY![bool; SPAN], T![app T![abs "x", TY![bool; SPAN], x; S![10, 20]], y; S![9, 23]]; S![0, 23]],
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
        assert_eq!(parse("(λx:Bool.x)", &env)?, parse(" λx:Bool.x", &env)?);
        Ok(())
    }

    #[test]
    fn test_pparse_aren_type() {
        check(
            "λx:(Bool).x",
            T![abs "x", TY![bool; SPAN], T![var 0; S![11, 12]]; S![0, 12]],
        );
    }

    #[test]
    fn test_parse_arrow_types() {
        // Bool → Bool
        let b_b_ty = TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN];
        check(
            "λf:Bool → Bool.λb:Bool.f b",
            T![abs "f", b_b_ty, T![abs "b", TY![bool; SPAN], T![app T![var 1; S![27, 28]], T![var 0; S![29, 30]]; S![27, 30]]; S![18, 30]]; S![0, 30]],
        );

        // arrow is right associative
        // Bool → Bool → Bool = Bool → (Bool → Bool)
        let b_b_b_ty = TY![abs TY![bool; SPAN], b_b_ty; SPAN];
        check(
            "λf:Bool → Bool → Bool.λb1:Bool.λb2:Bool.f b1 b2",
            T![
                abs
                "f",
                b_b_b_ty,
                T![
                    abs
                    "b1",
                    TY![bool; SPAN],
                    T![
                        abs
                        "b2",
                        TY![bool; SPAN],
                        T![
                            app
                            T![
                                app
                                T![var 2; S![47, 48]],
                                T![var 1; S![49, 51]];
                                S![47, 51]
                            ],
                            T![var 0; S![52, 54]];
                            S![47, 54]
                        ];
                        S![37, 54]
                    ];
                    S![27, 54]
                ];
            S![0, 54]
            ],
        );

        let b_b_b_ty_2 = TY![abs b_b_ty, TY![bool; SPAN]; SPAN];
        check(
            "λf:(Bool → Bool) → Bool.λb:Bool → Bool.f b",
            T![
                abs
                "f",
                b_b_b_ty_2,
                T![
                    abs
                    "b",
                    TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN],
                    T![
                        app
                        T![var 1; S![47, 48]],
                        T![var 0; S![49, 50]];
                        S![47, 50]
                    ];
                    S![29, 50]
                ];
                S![0, 50]
            ],
        );
    }

    #[test]
    fn test_parse_if() {
        check(
            "if
                (λx:Bool.x) true
            then
                λx:Bool.x
            else
                λx:Bool.false",
            T![
                if
                T![app T![abs "x", TY![bool; SPAN], T![var 0; S![29, 30]]; S![20, 30]], T![true; S![32, 36]]; S![19, 36]],
                T![abs "x", TY![bool; SPAN], T![var 0; S![79, 80]]; S![70, 80]],
                T![abs "x", TY![bool; SPAN], T![false; S![123, 128]]; S![114, 128]];
                S![0, 128]
            ],
        );
    }

    #[test]
    fn test_parse_base_type() {
        check(
            "λx:A.x",
            T![abs "x", TY![base "A"; SPAN], T![var 0; S![6, 7]]; S![0, 7]],
        );
        check(
            "λx:A → A.x",
            T![abs "x", TY![abs TY![base "A"; SPAN], TY![base "A"; SPAN]; SPAN], T![var 0; S![12, 13]]; S![0, 13]],
        );
    }

    #[test]
    fn test_parse_nats() {
        check("0", T![0; S![0, 1]]);
        check("1", T![succ T![0; S![0, 1]]; S![0, 1]]);
        check(
            "5",
            T![succ T![succ T![succ T![succ T![succ T![0; S![0, 1]]; S![0, 1]]; S![0, 1]]; S![0, 1]]; S![0, 1]]; S![0, 1]],
        );
        // We parse it, but the typechecker throws an error
        check("0 0", T![app T![0; S![0, 1]], T![0; S![2, 3]]; S![0, 3]]);
        check(
            "λx:Nat.x",
            T![abs "x", TY![nat; SPAN], T![var 0; S![8, 9]]; S![0, 9]],
        );
        check("pred 0", T![pred T![0; S![5, 6]]; S![0, 6]]);
        check("pred true", T![pred T![true; S![5, 9]]; S![0, 9]]);
        check("succ 0", T![succ T![0; S![5, 6]]; S![0, 6]]);
        check("iszero 0", T![iszero T![0; S![7, 8]]; S![0, 8]]);
        check(
            "iszero pred 0",
            T![iszero T![pred T![0; S![12, 13]]; S![7, 13]]; S![0, 13]],
        );
        check(
            "if iszero pred 0 then false else true",
            T![if T![iszero T![pred T![0; S![15, 16]]; S![10, 16]]; S![3, 16]], T![false; S![22, 27]], T![true; S![33, 37]]; S![0, 37]],
        );
    }

    #[test]
    fn test_parse_unit() {
        check("unit", T![unit; S![0, 4]]);
        check(
            "λx:Nat.unit",
            T![abs "x", TY![nat; SPAN], T![unit; S![8, 12]]; S![0, 12]],
        );
        check(
            "λx:Unit.x",
            T![abs "x", TY![unit; SPAN], T![var 0; S![9, 10]]; S![0, 10]],
        );
    }

    #[test]
    fn test_parse_ascription() {
        check(
            "true as Bool",
            T![asc T![true; S![0, 4]], TY![bool; SPAN]; S![0, 12]],
        );
        // Correct precedence
        check(
            "succ 0 as Nat",
            T![succ T![asc T![0; S![5, 6]], TY![nat; SPAN]; S![5, 13]]; S![0, 13]],
        );
        check(
            "(succ 0) as Nat",
            T![asc T![succ T![0; S![6, 7]]; S![1, 7]], TY![nat; SPAN]; S![1, 15]],
        );
        check(
            "λx:Bool.x as Bool",
            T![abs "x", TY![bool; SPAN], T![asc T![var 0; S![9, 10]], TY![bool; SPAN]; S![9, 18]]; S![0, 18]],
        );
        check(
            "(λx:Bool.x) as Bool → Bool",
            T![asc T![abs "x", TY![bool; SPAN], T![var 0; S![10, 11]]; S![1, 11]], TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN]; S![1, 29]],
        );
    }

    #[test]
    fn error_parse_ascription() {
        check_error("true as", "Expected a type, got `<eof>`");
    }

    #[test]
    fn test_parse_let_bindings() {
        check(
            "let x = true in x",
            T![let "x", T![true; S![8, 12]], T![var 0; S![16, 17]]; S![0, 17]],
        );
        check(
            "let not = λb:Bool.if b then false else true in not true",
            T![let "not", T![abs "b", TY![bool; SPAN], T![if T![var 0; S![22, 23]], T![false; S![29, 34]], T![true; S![40, 44]]; S![19, 44]]; S![10, 44]], T![app T![var 0; S![48, 51]], T![true; S![52, 56]]; S![48, 56]]; S![0, 56]],
        );
        check(
            "let x = let y = false in y in x",
            T![let "x", T![let "y", T![false; S![16, 21]], T![var 0; S![25, 26]]; S![8, 26]], T![var 0; S![30, 31]]; S![0, 31]],
        );
    }

    #[test]
    fn error_parse_let_bindings() {
        check_error("let x = x in x", "Variable `x` not bound");
    }

    #[test]
    fn test_parse_tuple() {
        check("{}", T![tuple; S![0, 2]]);
        check("{true}", T![tuple T![true; S![1, 5]]; S![0, 6]]);
        check(
            "{λ_:Bool.true, λ_:Bool.false}",
            T![tuple T![abs "_", TY![bool; SPAN], T![true; S![10, 14]]; S![1, 14]], T![abs "_", TY![bool; SPAN], T![false; S![25, 30]]; S![16, 30]]; S![0, 31]],
        );
        check(
            "{(λb:Bool.b) true}",
            T![tuple T![app T![abs "b", TY![bool; SPAN], T![var 0; S![11, 12]]; S![2, 12]], T![true; S![14, 18]]; S![1, 18]]; S![18, 19]],
        );
        check(
            "{true, false, true}",
            T![tuple T![true; S![1, 5]], T![false; S![7, 12]], T![true; S![14, 18]]; S![0, 19]],
        );
        // We accept trailing commas
        check("{0,}", T![tuple T![0; S![1, 2]]; S![0, 4]]);

        check(
            "λt:{Bool, Bool}.t",
            T![abs "t", TY![tuple TY![bool; SPAN], TY![bool; SPAN]; SPAN], T![var 0; S![17, 18]]; S![0, 18]],
        );
        check(
            "λt:{{Unit, Unit}, Bool}.t",
            T![abs "t", TY![tuple TY![tuple TY![unit; SPAN], TY![unit; SPAN]; SPAN], TY![bool; SPAN]; SPAN], T![var 0; S![25, 26]]; S![0, 26]],
        );
        check(
            "λt:{}.t",
            T![abs "t", TY![tuple; SPAN], T![var 0; S![7, 8]]; S![0, 8]],
        );
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
        check(
            "{true}.1",
            T![proj T![tuple T![true; S![1, 5]]; S![0, 6]], 1; S![0, 8]],
        );
        check(
            "{} as {Bool, Bool}.1 as Bool",
            T![asc T![proj T![asc T![tuple; S![0, 2]], TY![tuple TY![bool; SPAN], TY![bool; SPAN]; SPAN]; S![0, 19]], 1; S![0, 20]], TY![bool; SPAN]; S![0, 28]],
        );
        check(
            "{true}.1 as Bool",
            T![asc T![proj T![tuple T![true; S![1, 5]]; S![0, 6]], 1; S![0, 8]], TY![bool; SPAN]; S![0, 16]],
        );
        check(
            "{{true, unit}.1, 0}.2 as Nat",
            T![asc T![proj T![tuple T![proj T![tuple T![true; S![2, 6]], T![unit; S![8, 12]]; S![1, 13]], 1; S![1, 15]], T![0; S![17, 18]]; S![0, 19]], 2; S![0, 21]], TY![nat; SPAN]; S![0, 28]],
        );
        check(
            "{{true, unit}.1, 0}.1.1",
            T![proj T![proj T![tuple T![proj T![tuple T![true; S![2, 6]], T![unit; S![8, 12]]; S![1, 13]], 1; S![1, 15]], T![0; S![17, 18]]; S![0, 19]], 1; S![0, 21]], 1; S![0, 23]],
        );
    }
}
