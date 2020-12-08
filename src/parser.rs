use crate::term::{LTerm, Term};
use crate::{
    lexer::{tokenize, Token, TokenKind},
    Symbol, T,
};
use anyhow::{anyhow, Result};
use std::rc::Rc;

pub fn parse(input: &str) -> Result<LTerm> {
    let tokens = tokenize(input);
    let parser = Parser::new(&tokens);
    parser.parse()
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

    fn parse(mut self) -> Result<LTerm> {
        self.parse_term(true)
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

    fn parse_term(&mut self, parse_application: bool) -> Result<LTerm> {
        match self.current() {
            TokenKind::Ident if !parse_application => Ok(T![var self.next().text]),
            TokenKind::Ident => self.parse_application_or_var(),
            TokenKind::Lambda => self.parse_abstraction(),
            TokenKind::LParen if !parse_application => {
                self.bump();
                let term = self.parse_term(true)?;
                self.eat(TokenKind::RParen)?;
                Ok(term)
            }
            TokenKind::LParen => self.parse_application_or_var(),
            TokenKind::Eof => Err(anyhow!("Expected a term, got <eof>")),
            TokenKind::RParen | TokenKind::Error | TokenKind::Period | TokenKind::Whitespace => {
                Err(anyhow!("Expected a term, got `{}`", self.next().text))
            }
        }
    }

    fn parse_application_or_var(&mut self) -> Result<LTerm> {
        debug_assert!(
            matches!(self.current(), TokenKind::Ident | TokenKind::LParen),
            "parse_application_or_var should only be called on an Ident"
        );

        // If we're at an identifier at the end of the string, or following a ')'
        // We parse only a single variable
        if self.current() == TokenKind::Ident
            && matches!(self.nth(1), TokenKind::Eof | TokenKind::RParen)
        {
            return Ok(T![var self.next().text]);
        }

        let mut application_items = vec![];
        while !matches!(self.current(), TokenKind::Eof | TokenKind::RParen) {
            let term = self.parse_term(false)?;
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

    fn parse_abstraction(&mut self) -> Result<LTerm> {
        self.bump();
        let ident = Symbol::from(self.eat(TokenKind::Ident)?.text);
        self.eat(TokenKind::Period)?;
        let body = self.parse_term(true)?;
        Ok(T![abs ident, body])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::T;
    use std::rc::Rc;

    fn check(input: &str, expected: LTerm) {
        assert_eq!(parse(input).expect("Could not parse"), expected);
    }

    fn check_error(input: &str, expected: &str) {
        assert_eq!(
            parse(input)
                .expect_err("Shouldn't parse correctly")
                .to_string(),
            expected,
        );
    }

    #[test]
    fn parse_variable() {
        check("x", T![var "x"]);
    }

    #[test]
    fn parse_abstraction() {
        check("λx.x", T![abs "x", T![var "x"]]);
        check(r"\x.x", T![abs "x", T![var "x"]]);
    }

    #[test]
    fn parse_application() {
        let x = T![var "x"];
        check("x x", T![app x, x]);
    }

    #[test]
    fn parse_parenthesis() {
        let x = T![var "x"];
        let y = T![var "y"];
        check("(λx.x)y", T![app T![abs "x", x], y]);
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
        check_error("(x", "Expected a `)`, got <eof>");
        check_error(")", "Expected a term, got `)`");
    }

    #[test]
    fn error_parse_unknown_character() {
        check_error(";", "Expected a term, got `;`");
    }
}
