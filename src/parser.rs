use crate::{
    lexer::{tokenize, Token, TokenKind},
    term::Pattern,
    Symbol, T,
};
use crate::{
    term::{CaseBranches, LTerm, Term, TermKind},
    Error, ErrorKind, TY,
};
use crate::{types::Ty, Env};
use crate::{
    types::{LTy, TyKind},
    Span,
};
use std::{collections::HashMap, rc::Rc};

type Result<T> = std::result::Result<T, Error>;

macro_rules! error {
    ($msg:expr, $($arg:expr),*; $span:expr) => {
        Error::new(format!($msg, $($arg),*), $span, ErrorKind::Parser)
    };
    ($msg:expr; $span:expr) => {
        error!($msg,;$span)
    };
}

pub fn parse(input: &str, env: &mut Env) -> Result<LTerm> {
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

    fn parse(mut self, env: &mut Env) -> Result<LTerm> {
        let parsed = self.parse_application_or_var(true, env)?;

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

    fn parse_term(&mut self, env: &mut Env) -> Result<LTerm> {
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
                let term = self.parse_application_or_var(false, env)?;
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
                let mut term = self.parse_application_or_var(true, env)?;
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
            | TokenKind::Then
            | TokenKind::Else
            | TokenKind::Colon
            | TokenKind::Arrow
            | TokenKind::Wildcard
            | TokenKind::As
            | TokenKind::In
            | TokenKind::Assign
            | TokenKind::RBrace
            | TokenKind::Comma
            | TokenKind::Gt
            | TokenKind::FatArrow
            | TokenKind::Of
            | TokenKind::Pipe
            | TokenKind::Semicolon
            | TokenKind::LBracket
            | TokenKind::RBracket
            | TokenKind::RefAssign => {
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
                let cond = self.parse_application_or_var(false, env)?;
                self.eat(TokenKind::Then)?;
                let then = self.parse_application_or_var(false, env)?;
                self.eat(TokenKind::Else)?;
                let else_b = self.parse_application_or_var(false, env)?;
                let span = span.with_hi(else_b.span.hi);
                Ok(T![if cond, then, else_b; span])
            }
            TokenKind::Let => {
                let span = self.current_span();
                self.bump();
                let (p, p_span) = self.parse_pattern()?;
                self.eat(TokenKind::Assign)?;
                let t1 = self.parse_application_or_var(false, env)?;
                if self.current() == TokenKind::Semicolon {
                    let end = self.eat(TokenKind::Semicolon)?;
                    resolve_match_mut(&p, env, p_span)?;
                    Ok(T![var p, t1; span.with_hi(end.span.hi)])
                } else {
                    self.eat(TokenKind::In)?;
                    let mut env = resolve_match(&p, env, p_span)?;
                    let t2 = self.parse_application_or_var(false, &mut env)?;
                    let span = span.with_hi(t2.span.hi);
                    Ok(T![let p, t1, t2; span])
                }
            }
            TokenKind::LBrace => {
                let span = self.current_span();
                self.bump();
                let mut keys = vec![];
                let mut terms = HashMap::new();
                let mut comma_consumed = true;

                while self.current().can_start_term() {
                    let key = if self.nth(1) == TokenKind::Assign {
                        let (key, _) = self.eat_ident(false)?;
                        self.eat(TokenKind::Assign)?;
                        key
                    } else {
                        Symbol::from((terms.len() + 1).to_string())
                    };
                    let term = self.parse_application_or_var(false, env)?;
                    keys.push(Symbol::clone(&key));
                    terms.insert(key, term);
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
                    kind: TermKind::Record(terms, keys),
                    span,
                }))
            }
            TokenKind::Type => {
                let start = self.current_span();
                self.bump();
                let (ident, _) = self.eat_ident(false)?;
                self.eat(TokenKind::Assign)?;
                let ty = self.parse_type()?;
                let end = self.eat(TokenKind::Semicolon)?;
                Ok(Rc::new(Term {
                    span: start.with_hi(end.span.hi),
                    kind: TermKind::TypeDefinition(ident, ty),
                }))
            }
            TokenKind::Case => self.parse_case(env),
            // <l=t> as T
            TokenKind::Lt => {
                let start = self.current_span();
                self.bump();
                let (ident, _) = self.eat_ident(false)?;
                self.eat(TokenKind::Assign)?;
                let t = self.parse_application_or_var(false, env)?;
                let end = self.eat(TokenKind::Gt)?.span;
                Ok(Rc::new(Term {
                    span: start.with_hi(end.hi),
                    kind: TermKind::Variant(ident, t),
                }))
            }
            TokenKind::Fix => {
                let start = self.current_span();
                self.bump();
                let t = self.parse_term(env)?;
                let t_span = t.span;
                Ok(Rc::new(Term {
                    span: start.with_hi(t_span.hi),
                    kind: TermKind::Fix(t),
                }))
            }
            TokenKind::Letrec => {
                let start = self.current_span();
                self.bump();
                let (x, x_span) = self.eat_ident(false)?;
                self.eat(TokenKind::Colon)?;
                let ty = self.parse_type()?;
                self.eat(TokenKind::Assign)?;
                let mut fixenv = Env::with_parent(env);
                fixenv.insert_symbol(&x, x_span)?;
                let t1 = self.parse_application_or_var(false, &mut fixenv)?;
                if self.current() == TokenKind::Semicolon {
                    let end = self.eat(TokenKind::Semicolon)?;
                    env.insert_symbol(&x, x_span)?;
                    let t_span = t1.span;
                    Ok(Rc::new(Term {
                        span: start.with_hi(end.span.hi),
                        kind: TermKind::VariableDefinition(
                            Box::new(Pattern::Var(Symbol::clone(&x))),
                            Rc::new(Term {
                                span: x_span.with_hi(t_span.hi),
                                kind: TermKind::Fix(Rc::new(Term {
                                    span: x_span.with_hi(t_span.hi),
                                    kind: TermKind::Abstraction(x, ty, t1),
                                })),
                            }),
                        ),
                    }))
                } else {
                    self.eat(TokenKind::In)?;
                    let t2 = self.parse_application_or_var(false, &mut fixenv)?;
                    let t1_span = t1.span;
                    let t2_span = t2.span;
                    Ok(Rc::new(Term {
                        span: start.with_hi(t2_span.hi),
                        kind: TermKind::Let(
                            Box::new(Pattern::Var(Symbol::clone(&x))),
                            Rc::new(Term {
                                span: x_span.with_hi(t1_span.hi),
                                kind: TermKind::Fix(Rc::new(Term {
                                    span: x_span.with_hi(t1_span.hi),
                                    kind: TermKind::Abstraction(x, ty, t1),
                                })),
                            }),
                            t2,
                        ),
                    }))
                }
            }
            TokenKind::Nil => {
                let start = self.current_span();
                self.bump();
                self.eat(TokenKind::LBracket)?;
                let ty = self.parse_type()?;
                let end = self.eat(TokenKind::RBracket)?.span;
                Ok(Rc::new(Term {
                    span: start.with_hi(end.hi),
                    kind: TermKind::Nil(ty),
                }))
            }
            TokenKind::Cons => {
                let start = self.current_span();
                self.bump();
                self.eat(TokenKind::LBracket)?;
                let ty = self.parse_type()?;
                self.eat(TokenKind::RBracket)?;
                let t1 = self.parse_term(env)?;
                let t2 = self.parse_term(env)?;
                let t2_span = t2.span;
                Ok(Rc::new(Term {
                    span: start.with_hi(t2_span.hi),
                    kind: TermKind::Cons(t1, t2, ty),
                }))
            }
            TokenKind::IsNil => {
                let start = self.current_span();
                self.bump();
                self.eat(TokenKind::LBracket)?;
                let ty = self.parse_type()?;
                self.eat(TokenKind::RBracket)?;
                let t = self.parse_term(env)?;
                let t_span = t.span;
                Ok(Rc::new(Term {
                    span: start.with_hi(t_span.hi),
                    kind: TermKind::IsNil(t, ty),
                }))
            }
            TokenKind::Head => {
                let start = self.current_span();
                self.bump();
                self.eat(TokenKind::LBracket)?;
                let ty = self.parse_type()?;
                self.eat(TokenKind::RBracket)?;
                let t = self.parse_term(env)?;
                let t_span = t.span;
                Ok(Rc::new(Term {
                    span: start.with_hi(t_span.hi),
                    kind: TermKind::Head(t, ty),
                }))
            }
            TokenKind::Tail => {
                let start = self.current_span();
                self.bump();
                self.eat(TokenKind::LBracket)?;
                let ty = self.parse_type()?;
                self.eat(TokenKind::RBracket)?;
                let t = self.parse_term(env)?;
                let t_span = t.span;
                Ok(Rc::new(Term {
                    span: start.with_hi(t_span.hi),
                    kind: TermKind::Tail(t, ty),
                }))
            }
            TokenKind::Ref => {
                let start = self.current_span();
                self.bump();
                let t = self.parse_term(env)?;
                let t_span = t.span;
                Ok(Rc::new(Term {
                    span: start.with_hi(t_span.hi),
                    kind: TermKind::Ref(t),
                }))
            }
            TokenKind::Bang => {
                let start = self.current_span();
                self.bump();
                let t = self.parse_term(env)?;
                let t_span = t.span;
                Ok(Rc::new(Term {
                    span: start.with_hi(t_span.hi),
                    kind: TermKind::Deref(t),
                }))
            }
        }
    }

    fn parse_application_or_var(&mut self, allow_statements: bool, env: &mut Env) -> Result<LTerm> {
        let span = self.current_span();
        let mut application_items = vec![];
        while self.current().can_start_term() {
            let term = self.parse_term(env)?;
            let term = self.parse_post_term(term, env)?;
            application_items.push(term);
        }

        if application_items.is_empty() {
            let t = self.next();
            return Err(error!("Expected a term, got `{}`", t; t.span));
        }

        let mut application_items = application_items.into_iter();
        let t1 = application_items.next().unwrap();

        let t = match application_items.next() {
            Some(t2) => {
                let mut c_span = span.with_hi(t2.span.hi);
                application_items.fold(T![app t1, t2; c_span], move |acc, current| {
                    c_span = c_span.with_hi(current.span.hi);
                    T![app acc, current; c_span]
                })
            }
            None => t1,
        };

        if self.current() == TokenKind::Semicolon && allow_statements {
            self.bump();
            let mut env = Env::with_parent(env);
            env.insert_symbol("_", t.span)?;
            let t2 = self.parse_application_or_var(true, &mut env)?;
            let t_span = t.span;
            let t2_span = t2.span;
            Ok(Rc::new(Term {
                span: t_span.with_hi(t2_span.hi),
                kind: TermKind::Application(
                    Rc::new(Term {
                        span: t_span.with_hi(t2_span.hi),
                        kind: TermKind::Abstraction(
                            Symbol::from("_"),
                            Rc::new(Ty {
                                span: t_span,
                                kind: TyKind::Unit,
                            }),
                            t2,
                        ),
                    }),
                    t,
                ),
            }))
        } else {
            Ok(t)
        }
    }

    fn parse_pattern(&mut self) -> Result<(Box<Pattern>, Span)> {
        let start = self.current_span();
        match self.current() {
            TokenKind::Ident => {
                let t = self.next();
                let x = t.text;
                Ok((Box::new(Pattern::Var(x.into())), t.span))
            }
            TokenKind::LBrace => {
                self.next();
                let mut keys = vec![];
                let mut patterns = HashMap::new();
                while self.current() != TokenKind::Eof && self.current() != TokenKind::RBrace {
                    let (key, span) = if self.nth(1) == TokenKind::Assign {
                        let p = self.eat_ident(false)?;
                        self.eat(TokenKind::Assign)?;
                        p
                    } else {
                        (
                            Symbol::from((keys.len() + 1).to_string()),
                            self.current_span(),
                        )
                    };
                    if patterns.get(&key).is_some() {
                        return Err(error!("Key already matched against: `{}`", key; span));
                    }
                    let (p, _) = self.parse_pattern()?;
                    keys.push(Symbol::clone(&key));
                    patterns.insert(key, p);
                    if self.current() != TokenKind::RBrace {
                        self.eat(TokenKind::Comma)?;
                    }
                }
                let end = self.eat(TokenKind::RBrace)?.span;
                Ok((
                    Box::new(Pattern::Record(patterns, keys)),
                    start.with_hi(end.hi),
                ))
            }
            _ => {
                let t = self.next();
                Err(error!("Expected an identifier or `{{`, got `{}`", t; t.span))
            }
        }
    }

    fn parse_post_term(&mut self, mut t: LTerm, env: &mut Env) -> Result<LTerm> {
        loop {
            match self.current() {
                TokenKind::Period => {
                    self.bump();
                    let (elem, end) = if self.current() == TokenKind::Number {
                        let (n, end) = self.eat_number()?;
                        (Symbol::from(n.to_string()), end)
                    } else if self.current() == TokenKind::Ident {
                        self.eat_ident(false)?
                    } else {
                        let t = self.next();
                        return Err(
                            error!("Expected an identifier or number, got `{}`", t; t.span),
                        );
                    };
                    let span = t.span.with_hi(end.hi);
                    t = T![proj t, elem; span];
                }
                TokenKind::As => {
                    self.bump();
                    let ty = self.parse_type()?;
                    let span = t.span.with_hi(ty.span.hi);
                    t = T![asc t, ty; span];
                }
                TokenKind::RefAssign => {
                    self.bump();
                    let t2 = self.parse_application_or_var(false, env)?;
                    let span = t.span.with_hi(t.span.hi);
                    t = Rc::new(Term {
                        span,
                        kind: TermKind::RefAssign(t, t2),
                    })
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

    fn parse_ident(&mut self, env: &mut Env) -> Result<LTerm> {
        debug_assert_eq!(
            self.current(),
            TokenKind::Ident,
            "parse_ident expects to be called on an identifier"
        );
        let (s, span) = self.eat_ident(false)?;
        Ok(T![var self.lookup_ident(&s, env).map_err(|e| error!("{}", e; span))?; span])
    }

    fn lookup_ident(&self, s: &Symbol, env: &mut Env) -> std::result::Result<usize, String> {
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

    fn parse_abstraction(&mut self, env: &mut Env) -> Result<LTerm> {
        let span = self.current_span();
        self.bump();
        let (ident, _) = self.eat_ident(true)?;
        self.eat(TokenKind::Colon)?;
        let ty = self.parse_type()?;
        self.eat(TokenKind::Period)?;
        let mut env = Env::with_parent(env);
        env.insert_type(&ident, &ty)?;
        let body = self.parse_application_or_var(false, &mut env)?;
        let span = span.with_hi(body.span.hi);
        Ok(T![abs ident, ty, body; span])
    }

    fn parse_type(&mut self) -> Result<LTy> {
        let ty = match self.current() {
            TokenKind::LParen => {
                self.bump();
                let ty = self.parse_type()?;
                self.eat(TokenKind::RParen)?;
                ty
            }
            TokenKind::Ident => match self.next() {
                t if t.text == "Top" => Rc::new(Ty {
                    kind: TyKind::Top,
                    span: t.span,
                }),
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
                t if t.text == "List" => {
                    let span = t.span;
                    let inner_ty = self.parse_type()?;
                    Rc::new(Ty {
                        kind: TyKind::List(inner_ty),
                        span,
                    })
                }
                t if t.text == "Ref" => {
                    let span = t.span;
                    let inner_ty = self.parse_type()?;
                    Rc::new(Ty {
                        kind: TyKind::Ref(inner_ty),
                        span,
                    })
                }
                t => Rc::new(Ty {
                    kind: TyKind::Base(t.text.into()),
                    span: t.span,
                }),
            },
            TokenKind::LBrace => {
                let span = self.current_span();
                self.bump();
                let mut keys = vec![];
                let mut types = HashMap::new();
                let mut comma_consumed = true;

                while self.current().can_start_type() {
                    let key = if self.nth(1) == TokenKind::Colon {
                        let (key, _) = self.eat_ident(false)?;
                        self.eat(TokenKind::Colon)?;
                        key
                    } else {
                        Symbol::from((types.len() + 1).to_string())
                    };
                    let ty = self.parse_type()?;
                    keys.push(Symbol::clone(&key));
                    types.insert(key, ty);
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
                    kind: TyKind::Record(types, keys),
                    span,
                })
            }
            TokenKind::Lt => {
                let start = self.current_span();
                self.bump();
                let mut variants = HashMap::new();
                let mut keys = Vec::new();

                while self.current() != TokenKind::Eof && self.current() != TokenKind::Gt {
                    let (key, _) = self.eat_ident(false)?;
                    self.eat(TokenKind::Colon)?;
                    let ty = self.parse_type()?;
                    keys.push(Symbol::clone(&key));
                    variants.insert(key, ty);

                    if self.current() != TokenKind::Gt {
                        self.eat(TokenKind::Comma)?;
                    }
                }
                let end = self.eat(TokenKind::Gt)?.span;

                Rc::new(Ty {
                    span: start.with_hi(end.hi),
                    kind: TyKind::Variant(variants, keys),
                })
            }
            _ => {
                let t = self.next();
                return Err(error!("Expected a type, got `{}`", t; t.span));
            }
        };

        if self.current() == TokenKind::Arrow {
            self.bump();
            let rh_ty = self.parse_type()?;
            Ok(TY![abs ty, rh_ty; ty.span.with_hi(rh_ty.span.hi)])
        } else {
            Ok(ty)
        }
    }

    fn parse_case(&mut self, env: &mut Env) -> Result<LTerm> {
        let start = self.current_span();
        self.eat(TokenKind::Case)?;
        let case_v = self.parse_application_or_var(false, env)?;
        self.eat(TokenKind::Of)?;
        let (branches, keys, end) = self.parse_case_branches(env)?;
        Ok(Rc::new(Term {
            span: start.with_hi(end.hi),
            kind: TermKind::Case(case_v, branches, keys),
        }))
    }

    fn parse_case_branches(&mut self, env: &mut Env) -> Result<(CaseBranches, Vec<Symbol>, Span)> {
        let mut branches = HashMap::new();
        let mut keys = vec![];
        let start = self.current_span();
        let mut last_span;

        loop {
            let (kind, var, var_span) = if self.current() == TokenKind::Wildcard {
                let (t, span) = self.eat_ident(true)?;
                (Symbol::clone(&t), t, span)
            } else {
                self.eat(TokenKind::Lt)?;
                let (kind, _) = self.eat_ident(false)?;
                self.eat(TokenKind::Assign)?;
                let (var, var_span) = self.eat_ident(true)?;
                self.eat(TokenKind::Gt)?;
                (kind, var, var_span)
            };
            self.eat(TokenKind::FatArrow)?;
            let mut env = Env::with_parent(env);
            env.insert_symbol(&var, var_span)?;
            let term = self.parse_application_or_var(false, &mut env)?;
            last_span = term.span;
            branches.insert(Symbol::clone(&kind), (var, term));
            keys.push(kind);

            if self.current() == TokenKind::Pipe {
                self.eat(TokenKind::Pipe)?;
            } else {
                break;
            }
        }

        Ok((branches, keys, start.with_hi(last_span.hi)))
    }
}

fn resolve_match<'a>(p: &Pattern, env: &'a Env, span: Span) -> Result<Env<'a>> {
    let mut env = Env::with_parent(env);
    resolve_match_mut(p, &mut env, span)?;
    Ok(env)
}

fn resolve_match_mut(p: &Pattern, env: &mut Env, span: Span) -> Result<()> {
    match p {
        Pattern::Var(x) => {
            env.insert_symbol(x, span)?;
            Ok(())
        }
        Pattern::Record(recs, keys) => {
            for key in keys {
                resolve_match_mut(recs.get(key).unwrap(), env, span)?;
            }
            Ok(())
        }
    }
}

/// Regression tests
/// Run them normally with `cargo test`
///
/// When adding a new test, start with `check("input", expect![[]])`.
/// Run `cargo test`.
/// Make sure the result is the desired one.
/// Then fix the test with `UPDATE_EXPECT=1 cargo test`.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{term::term_to_string, S, T, TY};
    use expect_test::expect;
    use std::rc::Rc;

    const SPAN: Span = Span::new(0, 0);

    fn check(input: &str, expected: expect_test::Expect) {
        expected.assert_eq(&format!("{:?}", parse(input, &mut Env::new())));
    }

    fn check_env(input: &str, expected: expect_test::Expect, env: &mut Env) {
        expected.assert_eq(&format!("{:?}", parse(input, env)));
    }

    fn check_stringify(input: &str, expected: expect_test::Expect) {
        let mut env = Env::new();
        expected.assert_eq(
            &term_to_string(&parse(input, &mut env).expect("Couldn't parse"), &env)
                .expect("Couldn't stringify"),
        );
    }

    fn check_error(input: &str, expected: &str) {
        let error = parse(input, &mut Env::new()).expect_err("Shouldn't parse correctly");
        assert_eq!(
            error.to_string(),
            format!(
                "[{}-{}]SyntaxError: {}",
                error.span.lo, error.span.hi, expected
            ),
        );
    }

    fn check_error_with_kind(input: &str, expected: &str, error_kind: ErrorKind) {
        let error = parse(input, &mut Env::new()).expect_err("Shouldn't parse correctly");
        assert_eq!(
            error.to_string(),
            format!(
                "[{}-{}]{}Error: {}",
                error.span.lo, error.span.hi, error_kind, expected
            ),
        );
    }

    #[test]
    fn parse_variable() -> Result<()> {
        let mut env = Env::new();
        let id = parse("λx:Bool.x", &mut env)?;
        env.insert_term("id", &id)?;
        env.insert_type("id", &TY![abs TY![bool; SPAN], TY![bool; SPAN]; SPAN])?;
        assert_eq!(parse("id", &mut env)?, T![var 0; S![0, 2]]);
        Ok(())
    }

    #[test]
    fn parse_abstraction() {
        check(
            "λx:Bool.x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 10 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Term { span: Span { lo: 9, hi: 10 }, kind: Variable(0) }) })"#
            ]],
        );
        check(
            r"\x:Bool.x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 9 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 3, hi: 7 }, kind: Bool }, Term { span: Span { lo: 8, hi: 9 }, kind: Variable(0) }) })"#
            ]],
        );
        check(
            r"λx:Bool.λ_:Bool.x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 19 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Term { span: Span { lo: 9, hi: 19 }, kind: Abstraction(Atom('_' type=inline), Ty { span: Span { lo: 13, hi: 17 }, kind: Bool }, Term { span: Span { lo: 18, hi: 19 }, kind: Variable(1) }) }) })"#
            ]],
        );
    }

    #[test]
    fn parse_application() {
        check(
            "λx:Bool.x x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 12 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Term { span: Span { lo: 9, hi: 12 }, kind: Application(Term { span: Span { lo: 9, hi: 10 }, kind: Variable(0) }, Term { span: Span { lo: 11, hi: 12 }, kind: Variable(0) }) }) })"#
            ]],
        );
    }

    #[test]
    fn parse_parenthesis() {
        check(
            "λy:Bool.(λx:Bool.x) y",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 23 }, kind: Abstraction(Atom('y' type=inline), Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Term { span: Span { lo: 9, hi: 23 }, kind: Application(Term { span: Span { lo: 9, hi: 21 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 14, hi: 18 }, kind: Bool }, Term { span: Span { lo: 19, hi: 20 }, kind: Variable(0) }) }, Term { span: Span { lo: 22, hi: 23 }, kind: Variable(0) }) }) })"#
            ]],
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
    fn parse_single_term_inside_parentheses() {
        check(
            "(λx:Bool.x)",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 12 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 5, hi: 9 }, kind: Bool }, Term { span: Span { lo: 10, hi: 11 }, kind: Variable(0) }) })"#
            ]],
        );
    }

    #[test]
    fn parse_aren_type() {
        check(
            "λx:(Bool).x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 12 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 5, hi: 9 }, kind: Bool }, Term { span: Span { lo: 11, hi: 12 }, kind: Variable(0) }) })"#
            ]],
        );
    }

    #[test]
    fn parse_arrow_types() {
        // Bool → Bool
        check(
            "λf:Bool → Bool.λb:Bool.f b",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 30 }, kind: Abstraction(Atom('f' type=inline), Ty { span: Span { lo: 4, hi: 17 }, kind: Abstraction(Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Ty { span: Span { lo: 13, hi: 17 }, kind: Bool }) }, Term { span: Span { lo: 18, hi: 30 }, kind: Abstraction(Atom('b' type=inline), Ty { span: Span { lo: 22, hi: 26 }, kind: Bool }, Term { span: Span { lo: 27, hi: 30 }, kind: Application(Term { span: Span { lo: 27, hi: 28 }, kind: Variable(1) }, Term { span: Span { lo: 29, hi: 30 }, kind: Variable(0) }) }) }) })"#
            ]],
        );

        // arrow is right associative
        // Bool → Bool → Bool = Bool → (Bool → Bool)
        check(
            "λf:Bool → Bool → Bool.λb1:Bool.λb2:Bool.f b1 b2",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 54 }, kind: Abstraction(Atom('f' type=inline), Ty { span: Span { lo: 4, hi: 26 }, kind: Abstraction(Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Ty { span: Span { lo: 13, hi: 26 }, kind: Abstraction(Ty { span: Span { lo: 13, hi: 17 }, kind: Bool }, Ty { span: Span { lo: 22, hi: 26 }, kind: Bool }) }) }, Term { span: Span { lo: 27, hi: 54 }, kind: Abstraction(Atom('b1' type=inline), Ty { span: Span { lo: 32, hi: 36 }, kind: Bool }, Term { span: Span { lo: 37, hi: 54 }, kind: Abstraction(Atom('b2' type=inline), Ty { span: Span { lo: 42, hi: 46 }, kind: Bool }, Term { span: Span { lo: 47, hi: 54 }, kind: Application(Term { span: Span { lo: 47, hi: 51 }, kind: Application(Term { span: Span { lo: 47, hi: 48 }, kind: Variable(2) }, Term { span: Span { lo: 49, hi: 51 }, kind: Variable(1) }) }, Term { span: Span { lo: 52, hi: 54 }, kind: Variable(0) }) }) }) }) })"#
            ]],
        );

        check(
            "λf:(Bool → Bool) → Bool.λb:Bool → Bool.f b",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 50 }, kind: Abstraction(Atom('f' type=inline), Ty { span: Span { lo: 5, hi: 28 }, kind: Abstraction(Ty { span: Span { lo: 5, hi: 18 }, kind: Abstraction(Ty { span: Span { lo: 5, hi: 9 }, kind: Bool }, Ty { span: Span { lo: 14, hi: 18 }, kind: Bool }) }, Ty { span: Span { lo: 24, hi: 28 }, kind: Bool }) }, Term { span: Span { lo: 29, hi: 50 }, kind: Abstraction(Atom('b' type=inline), Ty { span: Span { lo: 33, hi: 46 }, kind: Abstraction(Ty { span: Span { lo: 33, hi: 37 }, kind: Bool }, Ty { span: Span { lo: 42, hi: 46 }, kind: Bool }) }, Term { span: Span { lo: 47, hi: 50 }, kind: Application(Term { span: Span { lo: 47, hi: 48 }, kind: Variable(1) }, Term { span: Span { lo: 49, hi: 50 }, kind: Variable(0) }) }) }) })"#
            ]],
        );
    }

    #[test]
    fn parse_if() {
        check(
            "if
                (λx:Bool.x) true
            then
                λx:Bool.x
            else
                λx:Bool.false",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 128 }, kind: If(Term { span: Span { lo: 19, hi: 36 }, kind: Application(Term { span: Span { lo: 19, hi: 31 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 24, hi: 28 }, kind: Bool }, Term { span: Span { lo: 29, hi: 30 }, kind: Variable(0) }) }, Term { span: Span { lo: 32, hi: 36 }, kind: True }) }, Term { span: Span { lo: 70, hi: 80 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 74, hi: 78 }, kind: Bool }, Term { span: Span { lo: 79, hi: 80 }, kind: Variable(0) }) }, Term { span: Span { lo: 114, hi: 128 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 118, hi: 122 }, kind: Bool }, Term { span: Span { lo: 123, hi: 128 }, kind: False }) }) })"#
            ]],
        );
    }

    #[test]
    fn parse_base_type() {
        check(
            "λx:A.x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 7 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 4, hi: 5 }, kind: Base(Atom('A' type=inline)) }, Term { span: Span { lo: 6, hi: 7 }, kind: Variable(0) }) })"#
            ]],
        );
        check(
            "λx:A → A.x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 13 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 4, hi: 11 }, kind: Abstraction(Ty { span: Span { lo: 4, hi: 5 }, kind: Base(Atom('A' type=inline)) }, Ty { span: Span { lo: 10, hi: 11 }, kind: Base(Atom('A' type=inline)) }) }, Term { span: Span { lo: 12, hi: 13 }, kind: Variable(0) }) })"#
            ]],
        );
    }

    #[test]
    fn parse_nats() {
        check(
            "0",
            expect![[r#"Ok(Term { span: Span { lo: 0, hi: 1 }, kind: Zero })"#]],
        );
        check(
            "1",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 1 }, kind: Succ(Term { span: Span { lo: 0, hi: 1 }, kind: Zero }) })"#
            ]],
        );
        check(
            "5",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 1 }, kind: Succ(Term { span: Span { lo: 0, hi: 1 }, kind: Succ(Term { span: Span { lo: 0, hi: 1 }, kind: Succ(Term { span: Span { lo: 0, hi: 1 }, kind: Succ(Term { span: Span { lo: 0, hi: 1 }, kind: Succ(Term { span: Span { lo: 0, hi: 1 }, kind: Zero }) }) }) }) }) })"#
            ]],
        );
        // We parse it, but the typechecker throws an error
        check(
            "0 0",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 3 }, kind: Application(Term { span: Span { lo: 0, hi: 1 }, kind: Zero }, Term { span: Span { lo: 2, hi: 3 }, kind: Zero }) })"#
            ]],
        );
        check(
            "λx:Nat.x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 9 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 4, hi: 7 }, kind: Nat }, Term { span: Span { lo: 8, hi: 9 }, kind: Variable(0) }) })"#
            ]],
        );
        check(
            "pred 0",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 6 }, kind: Pred(Term { span: Span { lo: 5, hi: 6 }, kind: Zero }) })"#
            ]],
        );
        check(
            "pred true",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 9 }, kind: Pred(Term { span: Span { lo: 5, hi: 9 }, kind: True }) })"#
            ]],
        );
        check(
            "succ 0",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 6 }, kind: Succ(Term { span: Span { lo: 5, hi: 6 }, kind: Zero }) })"#
            ]],
        );
        check(
            "iszero 0",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 8 }, kind: IsZero(Term { span: Span { lo: 7, hi: 8 }, kind: Zero }) })"#
            ]],
        );
        check(
            "iszero pred 0",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 13 }, kind: IsZero(Term { span: Span { lo: 7, hi: 13 }, kind: Pred(Term { span: Span { lo: 12, hi: 13 }, kind: Zero }) }) })"#
            ]],
        );
        check(
            "if iszero pred 0 then false else true",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 37 }, kind: If(Term { span: Span { lo: 3, hi: 16 }, kind: IsZero(Term { span: Span { lo: 10, hi: 16 }, kind: Pred(Term { span: Span { lo: 15, hi: 16 }, kind: Zero }) }) }, Term { span: Span { lo: 22, hi: 27 }, kind: False }, Term { span: Span { lo: 33, hi: 37 }, kind: True }) })"#
            ]],
        );
    }

    #[test]
    fn parse_unit() {
        check(
            "unit",
            expect![[r#"Ok(Term { span: Span { lo: 0, hi: 4 }, kind: Unit })"#]],
        );
        check(
            "λx:Nat.unit",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 12 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 4, hi: 7 }, kind: Nat }, Term { span: Span { lo: 8, hi: 12 }, kind: Unit }) })"#
            ]],
        );
        check(
            "λx:Unit.x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 10 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 4, hi: 8 }, kind: Unit }, Term { span: Span { lo: 9, hi: 10 }, kind: Variable(0) }) })"#
            ]],
        );
    }

    #[test]
    fn parse_ascription() {
        check(
            "true as Bool",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 12 }, kind: Ascription(Term { span: Span { lo: 0, hi: 4 }, kind: True }, Ty { span: Span { lo: 8, hi: 12 }, kind: Bool }) })"#
            ]],
        );
        // Correct precedence
        check(
            "succ 0 as Nat",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 13 }, kind: Succ(Term { span: Span { lo: 5, hi: 13 }, kind: Ascription(Term { span: Span { lo: 5, hi: 6 }, kind: Zero }, Ty { span: Span { lo: 10, hi: 13 }, kind: Nat }) }) })"#
            ]],
        );
        check(
            "(succ 0) as Nat",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 15 }, kind: Ascription(Term { span: Span { lo: 0, hi: 8 }, kind: Succ(Term { span: Span { lo: 6, hi: 7 }, kind: Zero }) }, Ty { span: Span { lo: 12, hi: 15 }, kind: Nat }) })"#
            ]],
        );
        check(
            "λx:Bool.x as Bool",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 18 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 4, hi: 8 }, kind: Bool }, Term { span: Span { lo: 9, hi: 18 }, kind: Ascription(Term { span: Span { lo: 9, hi: 10 }, kind: Variable(0) }, Ty { span: Span { lo: 14, hi: 18 }, kind: Bool }) }) })"#
            ]],
        );
        check(
            "(λx:Bool.x) as Bool → Bool",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 29 }, kind: Ascription(Term { span: Span { lo: 0, hi: 12 }, kind: Abstraction(Atom('x' type=inline), Ty { span: Span { lo: 5, hi: 9 }, kind: Bool }, Term { span: Span { lo: 10, hi: 11 }, kind: Variable(0) }) }, Ty { span: Span { lo: 16, hi: 29 }, kind: Abstraction(Ty { span: Span { lo: 16, hi: 20 }, kind: Bool }, Ty { span: Span { lo: 25, hi: 29 }, kind: Bool }) }) })"#
            ]],
        );
    }

    #[test]
    fn error_parse_ascription() {
        check_error("true as", "Expected a type, got `<eof>`");
    }

    #[test]
    fn parse_let_bindings() {
        check(
            "let x = true in x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 17 }, kind: Let(Var(Atom('x' type=inline)), Term { span: Span { lo: 8, hi: 12 }, kind: True }, Term { span: Span { lo: 16, hi: 17 }, kind: Variable(0) }) })"#
            ]],
        );
        check(
            "let not = λb:Bool.if b then false else true in not true",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 56 }, kind: Let(Var(Atom('not' type=inline)), Term { span: Span { lo: 10, hi: 44 }, kind: Abstraction(Atom('b' type=inline), Ty { span: Span { lo: 14, hi: 18 }, kind: Bool }, Term { span: Span { lo: 19, hi: 44 }, kind: If(Term { span: Span { lo: 22, hi: 23 }, kind: Variable(0) }, Term { span: Span { lo: 29, hi: 34 }, kind: False }, Term { span: Span { lo: 40, hi: 44 }, kind: True }) }) }, Term { span: Span { lo: 48, hi: 56 }, kind: Application(Term { span: Span { lo: 48, hi: 51 }, kind: Variable(0) }, Term { span: Span { lo: 52, hi: 56 }, kind: True }) }) })"#
            ]],
        );
        check(
            "let x = let y = false in y in x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 31 }, kind: Let(Var(Atom('x' type=inline)), Term { span: Span { lo: 8, hi: 26 }, kind: Let(Var(Atom('y' type=inline)), Term { span: Span { lo: 16, hi: 21 }, kind: False }, Term { span: Span { lo: 25, hi: 26 }, kind: Variable(0) }) }, Term { span: Span { lo: 30, hi: 31 }, kind: Variable(0) }) })"#
            ]],
        );

        check(
            "let {x} = {1} in x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 18 }, kind: Let(Record({Atom('1' type=inline): Var(Atom('x' type=inline))}, [Atom('1' type=inline)]), Term { span: Span { lo: 10, hi: 13 }, kind: Record({Atom('1' type=inline): Term { span: Span { lo: 11, hi: 12 }, kind: Succ(Term { span: Span { lo: 11, hi: 12 }, kind: Zero }) }}, [Atom('1' type=inline)]) }, Term { span: Span { lo: 17, hi: 18 }, kind: Variable(0) }) })"#
            ]],
        );
        check_stringify(
            "let {f=f, l=l} = {f=1, l=0} in f",
            expect![[r#"let {f=f, l=l} = {f=1, l=0} in f"#]],
        );

        let mut env = Env::new();
        check_env(
            "let x = 3; x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 12 }, kind: Application(Term { span: Span { lo: 0, hi: 10 }, kind: VariableDefinition(Var(Atom('x' type=inline)), Term { span: Span { lo: 8, hi: 9 }, kind: Succ(Term { span: Span { lo: 8, hi: 9 }, kind: Succ(Term { span: Span { lo: 8, hi: 9 }, kind: Succ(Term { span: Span { lo: 8, hi: 9 }, kind: Zero }) }) }) }) }, Term { span: Span { lo: 11, hi: 12 }, kind: Variable(0) }) })"#
            ]],
            &mut env,
        );
        check_env(
            "let a = 3; a",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 12 }, kind: Application(Term { span: Span { lo: 0, hi: 10 }, kind: VariableDefinition(Var(Atom('a' type=inline)), Term { span: Span { lo: 8, hi: 9 }, kind: Succ(Term { span: Span { lo: 8, hi: 9 }, kind: Succ(Term { span: Span { lo: 8, hi: 9 }, kind: Succ(Term { span: Span { lo: 8, hi: 9 }, kind: Zero }) }) }) }) }, Term { span: Span { lo: 11, hi: 12 }, kind: Variable(1) }) })"#
            ]],
            &mut env,
        );
    }

    #[test]
    fn error_parse_let_bindings() {
        check_error("let x = x in x", "Variable `x` not bound");
        check_error(
            "let {x=x, x=y} = {x=true} in x",
            "Key already matched against: `x`",
        );
        check_error_with_kind(
            "let {x,x} = {0, 0} in x",
            "Variable `x` already bound",
            ErrorKind::Name,
        );
        check_error_with_kind(
            "let {f=x,l=x} = {f=true, l=false} in x",
            "Variable `x` already bound",
            ErrorKind::Name,
        );
    }

    #[test]
    fn parse_record() {
        check(
            "{}",
            expect![[r#"Ok(Term { span: Span { lo: 0, hi: 2 }, kind: Record({}, []) })"#]],
        );
        check(
            "{true}",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 6 }, kind: Record({Atom('1' type=inline): Term { span: Span { lo: 1, hi: 5 }, kind: True }}, [Atom('1' type=inline)]) })"#
            ]],
        );
        check_stringify(
            "{λ_:Bool.true, λ_:Bool.false}",
            expect![[r#"{λ_:Bool.true, λ_:Bool.false}"#]],
        );
        check_stringify("{(λb:Bool.b) true}", expect![[r#"{(λb:Bool.b) true}"#]]);
        check_stringify(
            "{first=true, false, last=true}",
            expect![[r#"{first=true, false, last=true}"#]],
        );
        check_stringify(
            "{first=true, middle=false, last=true}",
            expect![[r#"{first=true, middle=false, last=true}"#]],
        );
        // We accept trailing commas
        check(
            "{0,}",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 4 }, kind: Record({Atom('1' type=inline): Term { span: Span { lo: 1, hi: 2 }, kind: Zero }}, [Atom('1' type=inline)]) })"#
            ]],
        );

        check_stringify(
            "λt:{x:Bool, y:Bool}.t",
            expect![[r#"λt:{x:Bool, y:Bool}.t"#]],
        );
        check_stringify("λt:{Bool, Bool}.t", expect![[r#"λt:{Bool, Bool}.t"#]]);
        check_stringify(
            "λt:{{Unit, Unit}, Bool}.t",
            expect![[r#"λt:{{Unit, Unit}, Bool}.t"#]],
        );
        check(
            "λt:{}.t",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 8 }, kind: Abstraction(Atom('t' type=inline), Ty { span: Span { lo: 4, hi: 6 }, kind: Record({}, []) }, Term { span: Span { lo: 7, hi: 8 }, kind: Variable(0) }) })"#
            ]],
        );
    }

    #[test]
    fn error_parse_record() {
        check_error("{", "Expected a term or `}`, got `<eof>`");
        check_error("{true", "Expected `,` or `}`, got `<eof>`");
        check_error("{true,", "Expected a term or `}`, got `<eof>`");
        check_error("{true,,", "Expected a term or `}`, got `,`");
        check_error("{true ) true}", "Expected `,` or `}`, got `)`");
        check_error("λt:{", "Expected a type or `}`, got `<eof>`");
        check_error("λt:{Bool", "Expected `,` or `}`, got `<eof>`");
    }

    #[test]
    fn parse_record_projection() {
        check(
            "{true}.1",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 8 }, kind: Projection(Term { span: Span { lo: 0, hi: 6 }, kind: Record({Atom('1' type=inline): Term { span: Span { lo: 1, hi: 5 }, kind: True }}, [Atom('1' type=inline)]) }, Atom('1' type=inline)) })"#
            ]],
        );
        check_stringify("{} as {Bool, Bool}.1 as Bool", expect![[r#"{}.1"#]]);
        check(
            "{true}.1 as Bool",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 16 }, kind: Ascription(Term { span: Span { lo: 0, hi: 8 }, kind: Projection(Term { span: Span { lo: 0, hi: 6 }, kind: Record({Atom('1' type=inline): Term { span: Span { lo: 1, hi: 5 }, kind: True }}, [Atom('1' type=inline)]) }, Atom('1' type=inline)) }, Ty { span: Span { lo: 12, hi: 16 }, kind: Bool }) })"#
            ]],
        );
        check_stringify(
            "{{true, unit}.1, 0}.2 as Nat",
            expect![[r#"{{true, unit}.1, 0}.2"#]],
        );
        check_stringify(
            "{{true, unit}.1, 0}.1.1",
            expect![[r#"{{true, unit}.1, 0}.1.1"#]],
        );
    }

    #[test]
    fn parse_definitions() {
        check(
            "let x = true; x",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 15 }, kind: Application(Term { span: Span { lo: 0, hi: 13 }, kind: VariableDefinition(Var(Atom('x' type=inline)), Term { span: Span { lo: 8, hi: 12 }, kind: True }) }, Term { span: Span { lo: 14, hi: 15 }, kind: Variable(0) }) })"#
            ]],
        );
        check(
            "type UU = Unit → Unit;",
            expect![[
                r#"Ok(Term { span: Span { lo: 0, hi: 24 }, kind: TypeDefinition(Atom('UU' type=inline), Ty { span: Span { lo: 10, hi: 23 }, kind: Abstraction(Ty { span: Span { lo: 10, hi: 14 }, kind: Unit }, Ty { span: Span { lo: 19, hi: 23 }, kind: Unit }) }) })"#
            ]],
        );
    }

    #[test]
    fn parse_variants() {
        check_stringify(
            "type MaybeBool = <some:Bool, none:Unit>;",
            expect![[r#"type MaybeBool = <some:Bool, none:Unit>;"#]],
        );
        check_stringify("<some=true>", expect![[r#"<some=true>"#]]);
        check_stringify("<none=unit>", expect![[r#"<none=unit>"#]]);
        check_stringify("<some=iszero 0>", expect![[r#"<some=iszero 0>"#]]);
    }

    #[test]
    fn error_parse_variant() {
        check_error("<some=true", "Expected a `>`, got `<eof>`");
        check_error("<some=", "Expected a term, got `<eof>`");
        check_error("<some", "Expected a `=`, got `<eof>`");
        check_error("<", "Expected an identifier, got `<eof>`");
    }

    #[test]
    fn parse_case_of() {
        check_stringify(
            r#"λb:MaybeNat.
                  case b of
                       <some=n> => <some=iszero n> as MaybeBool
                       | <none=_> => <none=unit> as MaybeBool
            "#,
            expect![[
                r#"λb:MaybeNat.case b of <some=n> ⇒ <some=iszero n> | <none=_> ⇒ <none=unit>"#
            ]],
        );

        check_stringify(
            r#"
            λb:MaybeNat.
                case b of
                    <some=_> => true
                    | _ => false
            "#,
            expect![[r#"λb:MaybeNat.case b of <some=_> ⇒ true | _ ⇒ false"#]],
        );
    }

    #[test]
    fn parse_fix() {
        check_stringify(
            "fix λf:Bool → Bool.λx:Bool.x",
            expect![[r#"fix λf:Bool → Bool.λx:Bool.x"#]],
        );
    }

    #[test]
    fn parse_letrec() {
        check_stringify(
            r#"letrec iseven: Nat → Bool =
                λx:Nat.
                    if iszero x then true
                    else if iszero (pred x) then false
                    else iseven (pred (pred x))
                in iseven 7"#,
            expect![[
                r#"let iseven = fix λiseven':Nat → Bool.λx:Nat.if iszero x then true else if iszero pred x then false else iseven' pred pred x in iseven 7"#
            ]],
        );

        check_stringify(
            r#"letrec iseven: Nat → Bool =
                λx:Nat.
                    if iszero x then true
                    else if iszero (pred x) then false
                    else iseven (pred (pred x));
                iseven 7
                "#,
            expect![[
                r#"let iseven = fix λiseven':Nat → Bool.λx:Nat.if iszero x then true else if iszero pred x then false else iseven' pred pred x; iseven 7"#
            ]],
        );
    }

    #[test]
    fn parse_lists() {
        check_stringify("nil[Bool]", expect![[r#"nil[Bool]"#]]);
        check_stringify(
            "cons[Bool] true (cons[Bool] false nil[Bool])",
            expect![[r#"cons[Bool] true cons[Bool] false nil[Bool]"#]],
        );
        check_stringify(
            "isnil[Bool] nil[Bool]",
            expect![[r#"isnil[Bool] nil[Bool]"#]],
        );
        check_stringify("head[Bool] nil[Bool]", expect![[r#"head[Bool] nil[Bool]"#]]);
        check_stringify("tail[Bool] nil[Bool]", expect![[r#"tail[Bool] nil[Bool]"#]]);
        check_stringify("λl:List Nat.l", expect![[r#"λl:List Nat.l"#]]);
        check_stringify("λf:List Nat → Nat.f", expect![[r#"λf:List Nat → Nat.f"#]]);
    }

    #[test]
    fn parse_references() {
        check_stringify("ref 0", expect![[r#"ref 0"#]]);
        check_stringify("let a = ref 3; !a", expect![[r#"let a = ref 3; !a"#]]);
        check_stringify(
            "let a = ref 3; a := 4",
            expect![[r#"let a = ref 3; a := 4"#]],
        );
        check_stringify("λa:Ref Nat.!a", expect![[r#"λa:Ref Nat.!a"#]]);
        check_stringify(
            "let a = ref 3; a := 4; !a",
            expect![[r#"(λ_:Unit.!a) (let a = ref 3; a := 4)"#]],
        );
    }
}
