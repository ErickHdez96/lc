use crate::term::{LTerm, Term};
use crate::Env;
use crate::{
    lexer::{tokenize, Token, TokenKind},
    Symbol, T,
};
use anyhow::{anyhow, Result};
use std::rc::Rc;

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
        self.parse_term(true, env)
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

    fn next_text(&mut self) -> &str {
        match self.next() {
            t if t.kind == TokenKind::Eof => "<eof>",
            t => t.text,
        }
    }

    fn bump(&mut self) {
        self.cursor += 1;
    }

    fn eat(&mut self, kind: TokenKind) -> Result<Token> {
        if self.current() == kind {
            Ok(self.next())
        } else {
            Err(anyhow!("Expected a `{}`, got {}", kind, self.next_text()))
        }
    }

    fn parse_term(&mut self, parse_application: bool, env: &Env) -> Result<LTerm> {
        match self.current() {
            TokenKind::Ident if !parse_application => self.parse_ident(env),
            TokenKind::Ident => self.parse_application_or_var(env),
            TokenKind::Lambda => self.parse_abstraction(env),
            TokenKind::LParen if !parse_application => {
                self.bump();
                let term = self.parse_term(true, env)?;
                self.eat(TokenKind::RParen)?;
                Ok(term)
            }
            TokenKind::LParen => self.parse_application_or_var(env),
            TokenKind::Eof => Err(anyhow!("Expected a term, got <eof>")),
            TokenKind::RParen | TokenKind::Error | TokenKind::Period | TokenKind::Whitespace => {
                Err(anyhow!("Expected a term, got `{}`", self.next().text))
            }
        }
    }

    fn parse_application_or_var(&mut self, env: &Env) -> Result<LTerm> {
        debug_assert!(
            matches!(self.current(), TokenKind::Ident | TokenKind::LParen),
            "parse_application_or_var should only be called on an Ident or an opening parentheses"
        );

        // If we're at an identifier at the end of the string, or following a ')'
        // We parse only a single variable
        if self.current() == TokenKind::Ident
            && matches!(self.nth(1), TokenKind::Eof | TokenKind::RParen)
        {
            return self.parse_ident(env);
        }

        let mut application_items = vec![];
        while !matches!(self.current(), TokenKind::Eof | TokenKind::RParen) {
            let term = self.parse_term(false, &env)?;
            application_items.push(term);
        }
        debug_assert!(
            application_items.len() >= 2,
            "At least two terms should have been parsed for an application"
        );

        let mut application_items = application_items.iter();
        let t1 = application_items.next().unwrap();
        let t2 = application_items.next().unwrap();

        Ok(application_items.fold(T![app t1, t2], |acc, current| T![app acc, current]))
    }

    fn parse_ident(&mut self, env: &Env) -> Result<LTerm> {
        debug_assert_eq!(
            self.current(),
            TokenKind::Ident,
            "parse_ident expects to be called on an identifier"
        );
        let s = self.next().text.into();
        Ok(T![var self.lookup_ident(s, env)?])
    }

    fn lookup_ident(&self, s: Symbol, env: &Env) -> Result<usize> {
        env.get_db_index(s)
            .ok_or_else(|| anyhow!("Variable `{}` not bound", s))
    }

    fn parse_abstraction(&mut self, env: &Env) -> Result<LTerm> {
        self.bump();
        let ident = Symbol::from(self.eat(TokenKind::Ident)?.text);
        self.eat(TokenKind::Period)?;
        let mut env = Env::with_parent(env);
        env.insert_local(ident);
        let body = self.parse_term(true, &env)?;
        Ok(T![abs ident, body])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::T;
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
            expected,
        );
    }

    #[test]
    fn parse_variable() -> Result<()> {
        let mut env = Env::new();
        let id = parse("λx.x", &env)?;
        env.insert_variable("id", id);
        assert_eq!(parse("id", &env)?, T![var 0]);
        Ok(())
    }

    #[test]
    fn parse_abstraction() {
        check("λx.x", T![abs "x", T![var 0]]);
        check(r"\x.x", T![abs "x", T![var 0]]);
    }

    #[test]
    fn parse_application() {
        let x = T![var 0];
        check("λx.x x", T![abs "x", T![app x, x]]);
    }

    #[test]
    fn parse_parenthesis() {
        let x = T![var 0];
        let y = T![var 0];
        check("λy.(λx.x) y", T![abs "y", T![app T![abs "x", x], y]]);
    }

    #[test]
    fn error_parse_abstraction_no_body() {
        check_error("λx.", "Expected a term, got <eof>");
        check_error("λx", "Expected a `.`, got <eof>");
        check_error("λ", "Expected a `<ident>`, got <eof>");
    }

    #[test]
    fn error_parse_unmatched_parens() {
        check_error("(", "Expected a term, got <eof>");
        check_error("(λx.x", "Expected a `)`, got <eof>");
        check_error(")", "Expected a term, got `)`");
    }

    #[test]
    fn error_parse_unknown_character() {
        check_error(";", "Expected a term, got `;`");
    }
}
