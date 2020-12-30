use crate::{
    terminal::{Color, Style},
    Span,
};
use std::fmt;
use unicode_width::UnicodeWidthStr;

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
    Name,
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
        write!(
            f,
            "[{}-{}]{}Error: {}",
            self.span.lo, self.span.hi, self.kind, self.msg
        )
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
                Self::Name => "Name",
            }
        )
    }
}

pub fn print_error(error: &Error, source: &str) {
    // Runtime and type errors have Span(0, 0) currently
    if error.span.hi - error.span.lo > 0 && (error.span.hi as usize) < source.len() {
        let line = &source[..error.span.lo as usize].chars().fold(1, |acc, c| {
            if c == '\n' {
                acc + 1
            } else {
                acc
            }
        });

        let content = &source[error.span.lo as usize..error.span.hi as usize];

        eprintln!(
            " {}{} |{} {}",
            Style::new().bold().color(Color::BrightBlue),
            line,
            Style::new(),
            content,
        );

        let actual_offset = 4 + line.to_string().len();
        let actual_width = UnicodeWidthStr::width(content);

        let error_signal = if actual_width > 2 {
            format!("^{}^", "-".repeat(actual_width - 2))
        } else {
            "^".repeat(std::cmp::max(actual_width, 1))
        };
        eprintln!(
            "{}{}{}{}",
            " ".repeat(actual_offset),
            Style::new().bold().color(Color::BrightRed),
            error_signal,
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

pub fn print_error_repl(error: &Error, source: &str) {
    // Runtime and type errors have Span(0, 0) currently
    if error.span.hi - error.span.lo > 0 {
        let actual_offset = UnicodeWidthStr::width(&source[..error.span.lo as usize]);
        let actual_width =
            UnicodeWidthStr::width(&source[error.span.lo as usize..error.span.hi as usize]);

        let error_signal = if actual_width > 2 {
            format!("^{}^", "-".repeat(actual_width - 2))
        } else {
            "^".repeat(std::cmp::max(actual_width, 1))
        };

        eprintln!(
            "{}{}{}{}",
            " ".repeat(actual_offset + 3),
            Style::new().bold().color(Color::BrightRed),
            error_signal,
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
