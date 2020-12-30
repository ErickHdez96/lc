mod repl;
use lc::{
    env::{base_env, TyEnv},
    parse, print_error,
    term::{eval, term_to_string},
    types::type_of,
    Env,
};
use repl::run_repl;
use std::{fmt, fs, io, path::Path};

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

fn run_file(file_path: impl AsRef<Path>) -> Result<(Env<'static>, TyEnv<'static>), Error> {
    env_logger::init();
    let file_path = file_path.as_ref();
    let content = fs::read_to_string(file_path)?;

    let (mut env, mut tyenv) = base_env();

    match parse(&content, &mut env)
        .and_then(|p| eval(&p, &mut env, &mut tyenv))
        .and_then(|p| {
            Ok((
                term_to_string(&p, &env)?,
                type_of(&p, &mut env, &mut tyenv)?,
            ))
        }) {
        Ok((term, ty)) => println!("{} : {}", term, ty),
        Err(e) => print_error(&e, &content),
    }

    Ok((env, tyenv))
}

fn main() {
    let (mut env, mut tyenv) = if let Some(file) = std::env::args().nth(1) {
        match run_file(file) {
            Ok(envs) => envs,
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(1);
            }
        }
    } else {
        base_env()
    };
    run_repl(&mut env, &mut tyenv);
}
