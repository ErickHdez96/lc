use anyhow::Result;
use lc::{
    env::Env,
    parser::parse,
    term::{eval, Term},
    T,
};
use log::{error, warn};
use rustyline::{error::ReadlineError, Editor};
use std::path::PathBuf;
use std::rc::Rc;

pub fn run_repl() -> Result<()> {
    env_logger::init();
    let mut rl = init_rustyline();
    println!("Hello! Welcome to the lambda calculus evaluator");

    let mut env = Env::new();
    let tru = T![abs "t", T![abs "f", T![var "t"]]];
    let fls = T![abs "t", T![abs "f", T![var "f"]]];
    let not = T![abs "b", T![app T![app T![var "b"], fls], tru]];
    let and = T![abs "b", T![abs "c", T![app T![app T![var "b"], T![var "c"]], T![var "false"]]]];
    let or = T![abs "b", T![abs "c", T![app T![app T![var "b"], T![var "true"]], T![var "c"]]]];
    env.insert("true", tru);
    env.insert("false", fls);
    env.insert("not", not);
    env.insert("and", and);
    env.insert("or", or);

    loop {
        let input = rl.readline(">> ");

        match input {
            Ok(line) => match line.as_ref() {
                r"\q" => {
                    println!("Bye!");
                    break;
                }
                line => {
                    rl.add_history_entry(line);
                    match parse(line).and_then(|p| eval(p, &env)) {
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
    dirs::cache_dir().map(|d| d.with_file_name(".monkey_history"))
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
