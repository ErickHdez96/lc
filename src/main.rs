mod repl;
use std::{fmt, fs, io, path::Path};

use lc::{
    env::{base_env, base_tyenv},
    parse,
    term::{eval, term_to_string},
    types::type_of,
};
use repl::run_repl;

#[derive(Debug)]
enum Error {
    Io(io::Error),
    Lc(lc::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => e.fmt(f),
            Self::Lc(e) => e.fmt(f),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(io: io::Error) -> Self {
        Self::Io(io)
    }
}

impl From<lc::Error> for Error {
    fn from(lc: lc::Error) -> Self {
        Self::Lc(lc)
    }
}

fn run_file(file_path: impl AsRef<Path>) -> Result<(), Error> {
    env_logger::init();
    let file_path = file_path.as_ref();
    let content = fs::read_to_string(file_path)?;

    let mut env = base_env();
    let mut tyenv = base_tyenv();

    let (term, ty) = parse(&content, &mut env)
        .and_then(|p| eval(&p, &mut env, &mut tyenv))
        .and_then(|p| {
            Ok((
                term_to_string(&p, &env)?,
                type_of(&p, &mut env, &mut tyenv)?,
            ))
        })?;

    println!("{} : {}", term, ty);

    Ok(())
}

fn main() {
    if let Some(file) = std::env::args().nth(1) {
        if let Err(e) = run_file(file) {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    } else {
        run_repl();
    }
}
