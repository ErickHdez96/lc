use std::fmt;

#[derive(Debug, PartialEq, Eq)]
pub struct Error {
    pub msg: String,
    pub kind: ErrorKind,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    Parser,
    Runtime,
    Type,
}

impl Error {
    pub fn new(msg: impl Into<String>, kind: ErrorKind) -> Self {
        Self {
            msg: msg.into(),
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
                Self::Parser => "Parser",
                Self::Runtime => "Runtime",
                Self::Type => "Type",
            }
        )
    }
}

impl std::error::Error for Error {}
