use crate::Span;
use logos::Logos;
use std::convert::TryFrom;

pub fn tokenize(input: &str) -> Vec<Token> {
    let mut tokens = vec![];
    let mut lexer: logos::Lexer<'_, TokenKind> = TokenKind::lexer(input);

    while let Some(tok) = lexer.next() {
        let span = lexer.span();
        let lo = u32::try_from(span.start).expect("Lc can't handle files larger than 4GB");
        let hi = u32::try_from(span.end).expect("Lc can't handle files larger than 4GB");
        tokens.push(Token {
            kind: tok,
            text: lexer.slice(),
            span: Span::new(lo, hi),
        });
    }

    tokens
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Token<'input> {
    pub kind: TokenKind,
    pub text: &'input str,
    pub span: Span,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Logos)]
pub enum TokenKind {
    #[regex(r"\s+", logos::skip)]
    Whitespace,

    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("succ")]
    Succ,
    #[token("pred")]
    Pred,
    #[token("iszero")]
    IsZero,
    #[token("unit")]
    Unit,
    #[token("as")]
    As,
    #[token("let")]
    Let,
    #[token("in")]
    In,
    #[token("type")]
    Type,
    #[token("case")]
    Case,
    #[token("of")]
    Of,
    #[token("fix")]
    Fix,
    #[token("letrec")]
    Letrec,
    #[token("nil")]
    Nil,
    #[token("cons")]
    Cons,
    #[token("isnil")]
    IsNil,
    #[token("head")]
    Head,
    #[token("tail")]
    Tail,
    #[token("ref")]
    Ref,

    #[regex("[0-9]+")]
    Number,

    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*'*")]
    Ident,

    #[token(":=")]
    RefAssign,
    #[token(".")]
    Period,
    #[token(",")]
    Comma,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token(";")]
    Semicolon,
    #[token(":")]
    Colon,
    #[token("!")]
    Bang,

    #[regex(r"λ|\\")]
    Lambda,
    #[regex("(→|->)")]
    Arrow,
    #[regex("(=>|⇒)")]
    FatArrow,
    #[token("=")]
    Assign,
    #[token("|")]
    Pipe,
    #[regex("_")]
    Wildcard,

    #[error]
    Error,

    Eof,
}

impl TokenKind {
    pub fn can_start_term(self) -> bool {
        matches!(
            self,
            TokenKind::Lambda
                | TokenKind::True
                | TokenKind::False
                | TokenKind::If
                | TokenKind::Ident
                | TokenKind::LParen
                | TokenKind::Number
                | TokenKind::IsZero
                | TokenKind::Pred
                | TokenKind::Succ
                | TokenKind::Unit
                | TokenKind::Let
                | TokenKind::LBrace
                | TokenKind::Type
                | TokenKind::Case
                | TokenKind::Lt
                | TokenKind::Fix
                | TokenKind::Letrec
                | TokenKind::Nil
                | TokenKind::Cons
                | TokenKind::IsNil
                | TokenKind::Head
                | TokenKind::Tail
                | TokenKind::Bang
                | TokenKind::Ref
        )
    }

    pub fn can_start_type(self) -> bool {
        matches!(
            self,
            TokenKind::Ident | TokenKind::LParen | TokenKind::LBrace
        )
    }
}

impl<'input> std::fmt::Display for Token<'input> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.kind == TokenKind::Eof {
            write!(f, "<eof>")
        } else {
            self.text.fmt(f)
        }
    }
}

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TokenKind::*;
        write!(
            f,
            "{}",
            match self {
                Whitespace => "<whitespace>",
                Lambda => "λ",
                True => "true",
                False => "false",
                If => "if",
                Then => "then",
                Else => "else",
                Case => "case",
                Of => "of",
                Ident => "<ident>",
                Period => ".",
                Comma => ",",
                LParen => "(",
                RParen => ")",
                LBrace => "{",
                RBrace => "}",
                LBracket => "[",
                RBracket => "]",
                Lt => "<",
                Gt => ">",
                Semicolon => ";",
                Colon => ":",
                Arrow => "→",
                FatArrow => "⇒",
                Assign => "=",
                Pipe => "|",
                Wildcard => "_",
                Succ => "succ",
                Pred => "pred",
                Unit => "unit",
                As => "as",
                Let => "let",
                In => "in",
                Type => "type",
                IsZero => "iszero",
                Fix => "fix",
                Letrec => "letrec",
                Nil => "nil",
                Cons => "cons",
                IsNil => "isnil",
                Head => "head",
                Tail => "tail",
                Ref => "ref",
                Bang => "!",
                RefAssign => ":=",
                Number => "<number>",
                Error => "<unknown char>",
                Eof => "<eof>",
            }
        )
    }
}

impl<'a> std::default::Default for Token<'a> {
    fn default() -> Self {
        Self {
            text: "",
            span: Span::new(0, 0),
            kind: TokenKind::default(),
        }
    }
}

impl std::default::Default for TokenKind {
    fn default() -> Self {
        Self::Eof
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(input: &str, expected: Vec<TokenKind>) {
        assert_eq!(
            tokenize(input).iter().map(|t| t.kind).collect::<Vec<_>>(),
            expected
        );
    }

    #[test]
    fn test_lexer() {
        use TokenKind::*;

        check("", vec![]);
        check(" ", vec![]);
        check("λ", vec![Lambda]);
        check(r"\", vec![Lambda]);
        check("→", vec![Arrow]);
        check("->", vec![Arrow]);
        check("=>", vec![FatArrow]);
        check("⇒", vec![FatArrow]);
        check("_", vec![Wildcard]);
        check("x", vec![Ident]);
        check("true", vec![True]);
        check("false", vec![False]);
        check("if", vec![If]);
        check("then", vec![Then]);
        check("else", vec![Else]);
        check("iszero", vec![IsZero]);
        check("pred", vec![Pred]);
        check("succ", vec![Succ]);
        check("case", vec![Case]);
        check("of", vec![Of]);
        check("0", vec![Number]);
        check("10", vec![Number]);
        check("unit", vec![Unit]);
        check("as", vec![As]);
        check("let", vec![Let]);
        check("in", vec![In]);
        check("type", vec![Type]);
        check("fix", vec![Fix]);
        check("letrec", vec![Letrec]);
        check("ref", vec![Ref]);
        check(":=", vec![RefAssign]);
        check("!", vec![Bang]);
        check(".", vec![Period]);
        check(",", vec![Comma]);
        check("(", vec![LParen]);
        check(")", vec![RParen]);
        check("{", vec![LBrace]);
        check("}", vec![RBrace]);
        check("[", vec![LBracket]);
        check("]", vec![RBracket]);
        check("<", vec![Lt]);
        check(">", vec![Gt]);
        check(";", vec![Semicolon]);
        check(":", vec![Colon]);
        check("=", vec![Assign]);
        check("|", vec![Pipe]);
        check(
            "(λx.x) y",
            vec![LParen, Lambda, Ident, Period, Ident, RParen, Ident],
        );

        assert_eq!(
            tokenize("x"),
            vec![Token {
                kind: Ident,
                span: Span::new(0, 1),
                text: "x"
            }]
        );

        assert_eq!(
            tokenize("true"),
            vec![Token {
                kind: True,
                span: Span::new(0, 4),
                text: "true"
            }]
        );
    }
}
