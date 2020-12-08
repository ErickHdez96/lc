mod repl;
use anyhow::Result;
use repl::run_repl;

fn main() -> Result<()> {
    run_repl()
}
