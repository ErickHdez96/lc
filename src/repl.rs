use anyhow::Result;
use lc::term::term_to_string;
use lc::{env::base_env, parser::parse, term::eval};
use log::{error, warn};
use rustyline::{error::ReadlineError, Editor};
use std::path::PathBuf;

pub fn run_repl() -> Result<()> {
    env_logger::init();
    let mut rl = init_rustyline();
    println!("Hello! Welcome to the lambda calculus evaluator");

    let env = base_env();

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
                    match parse(line)
                        .and_then(|p| eval(p, &env))
                        .and_then(|p| term_to_string(&p, &env))
                    {
                        Ok(parsed) => println!("{}", parsed),
                        Err(e) => eprintln!("{}", e),
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

    Ok(())
}

fn get_history_file_path() -> Option<PathBuf> {
    dirs::cache_dir().map(|d| d.with_file_name(".lc_history"))
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
