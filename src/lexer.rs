use logos::Logos;

pub fn tokenize(input: &str) -> Vec<Token> {
    let mut tokens = vec![];
    let mut lexer = TokenKind::lexer(input);

    while let Some(tok) = lexer.next() {
        tokens.push(Token {
            kind: tok,
            text: lexer.slice(),
        });
    }

    tokens
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Token<'input> {
    pub kind: TokenKind,
    pub text: &'input str,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Logos)]
pub enum TokenKind {
    #[regex(r"\s+", logos::skip)]
    Whitespace,

    #[regex(r"λ|\\")]
    Lambda,

    #[regex(r"[a-zA-Z][a-zA-Z0-9]*'*")]
    Ident,

    #[token(".")]
    Period,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[error]
    Error,

    Eof,
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
                Ident => "<ident>",
                Period => ".",
                LParen => "(",
                RParen => ")",
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
        check("x", vec![Ident]);
        check("true", vec![Ident]);
        check(".", vec![Period]);
        check("(", vec![LParen]);
        check(")", vec![RParen]);
        check(
            "(λx.x) y",
            vec![LParen, Lambda, Ident, Period, Ident, RParen, Ident],
        );

        assert_eq!(
            tokenize("x"),
            vec![Token {
                kind: Ident,
                text: "x"
            }]
        );
    }
}
