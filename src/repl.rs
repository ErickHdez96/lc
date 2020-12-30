use lc::{env::TyEnv, parser::parse, print_error_repl, term::eval, Env};
use lc::{term::term_to_string, types::type_of};
use log::{error, warn};
use rustyline::{error::ReadlineError, Editor};
use std::path::PathBuf;

pub fn run_repl(env: &mut Env, tyenv: &mut TyEnv) {
    let mut rl = init_rustyline();
    println!("Hello! Welcome to the lambda calculus evaluator");

    loop {
        let input = rl.readline(">> ");

        match input {
            Ok(line) => match line.trim() {
                r"\q" => {
                    println!("Bye!");
                    break;
                }
                // Ignore empty lines
                "" => {}
                line => {
                    rl.add_history_entry(line);
                    match parse(line, env)
                        .and_then(|p| eval(&p, env, tyenv))
                        .and_then(|p| Ok((term_to_string(&p, &env)?, type_of(&p, env, tyenv)?)))
                    {
                        Ok((term, ty)) => println!("{} : {}", term, ty),
                        Err(e) => print_error_repl(&e, line),
                    }
                }
            },
            // <Ctrl-C> | <Ctrl-D>
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => {
                println!("Bye!");
                break;
            }
            Err(err) => {
                error!("Unexpected error: {:?}", err);
                break;
            }
        }
    }

    match get_history_file_path() {
        Some(file) => {
            if let Err(e) = rl.save_history(&file) {
                warn!("Failed to save repl history: {:?}", e);
            }
        }
        None => warn!("Failed to save repl history"),
    }
}

fn get_history_file_path() -> Option<PathBuf> {
    dirs::cache_dir().map(|d| d.join("lc_history"))
}

fn init_rustyline() -> Editor<()> {
    let mut rl = Editor::<()>::new();

    match get_history_file_path() {
        Some(ref mut history_file) => {
            if history_file.is_file() {
                if let Err(e) = rl.load_history(&history_file) {
                    warn!("Failed to load previous history: {}", e);
                }
            }
        }
        None => {
            warn!("Failed to open cache dir");
        }
    }

    rl
}
