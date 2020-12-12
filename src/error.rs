use crate::{
    terminal::{Color, Style},
    Span,
};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    pub msg: String,
    pub span: Span,
    pub kind: ErrorKind,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    Parser,
    Runtime,
    Type,
}

impl Error {
    pub fn new(msg: impl Into<String>, span: Span, kind: ErrorKind) -> Self {
        Self {
            msg: msg.into(),
            span,
            kind,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}Error: {}", self.kind, self.msg)
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Parser => "Syntax",
                Self::Runtime => "Runtime",
                Self::Type => "Type",
            }
        )
    }
}

// TODO: If there are multiple lines, print the corresponding source line
// Also if the input was from the interactive repl, but piped to it
pub fn print_error(error: &Error, _source: &str) {
    // Runtime and type errors have Span(0, 0) currently
    if error.span.hi - error.span.lo > 0 {
        eprintln!(
            "{}{}{}{}",
            " ".repeat(error.span.lo as usize + 3),
            Style::new().bold().color(Color::BrightRed),
            "↑".repeat(error.span.hi as usize - error.span.lo as usize),
            Style::new(),
        );
    }
    eprintln!(
        "{}{}Error:{} {}",
        Style::new().bold().color(Color::BrightRed),
        error.kind,
        Style::new(),
        error.msg,
    );
}

impl std::error::Error for Error {}
