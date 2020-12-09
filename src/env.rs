use crate::term::{rm_names, LTerm};
use crate::Symbol;
use anyhow::Result;
use log::error;
use std::collections::HashMap;

/// Terms are stored along with their calculated de Bruijn index
#[derive(Debug, Default)]
pub struct Env<'a> {
    pub context: HashMap<Symbol, usize>,
    pub vars: Vec<LTerm>,
    pub names: Vec<Symbol>,
    pub parent: Option<&'a Env<'a>>,
}

impl<'a> Env<'a> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_parent(parent: &'a Env<'a>) -> Self {
        Self {
            parent: Some(parent),
            vars: Vec::new(),
            names: Vec::with_capacity(1),
            // Every lambda is only allowed to have one variable
            // Only the root may have multiple.
            context: HashMap::with_capacity(1),
        }
    }

    pub fn get_name_from_db_index(&self, s: usize) -> Option<Symbol> {
        self.names.get(s).cloned().or_else(|| {
            self.parent.and_then(|p| {
                s.checked_sub(std::cmp::max(self.names.len(), 1))
                    .and_then(|s| p.get_name_from_db_index(s))
            })
        })
    }

    pub fn get_from_db_index(&self, s: usize) -> Option<LTerm> {
        self.vars.get(s).cloned().or_else(|| {
            self.parent.and_then(|p| {
                s.checked_sub(std::cmp::max(self.vars.len(), 1))
                    .and_then(|s| p.get_from_db_index(s))
            })
        })
    }

    pub fn get(&self, s: impl Into<Symbol>) -> Option<LTerm> {
        let s = s.into();
        if let Some(&idx) = self.context.get(&s) {
            self.vars.get(idx).cloned()
        } else {
            self.parent.and_then(|p| p.get(s))
        }
    }

    pub fn insert_local(&mut self, k: impl Into<Symbol>) {
        let db_idx = self.context.len();
        let k = k.into();
        self.context.insert(k, db_idx);
        self.names.push(k);
    }

    pub fn insert_variable(&mut self, k: impl Into<Symbol>, t: LTerm) {
        let k = k.into();
        let db_idx = self.vars.len();
        self.context.insert(k, db_idx);
        self.vars.push(t);
        self.names.push(k);
    }

    /// Get the de Bruijn index of the term pointed to by `name`.
    ///
    /// The index is calculated by the depth of the search + the original db_idx.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use lc::env::Env;
    /// use lc::{T, Term};
    /// use std::rc::Rc;
    ///
    /// let mut env_1 = Env::new();
    /// let id = T![abs "x", T![var "x"]];
    /// env_1.insert_variable("id", id.clone());
    /// assert_eq!(env_1.get_db_index("id"), Some(0));
    ///
    /// let mut env_2 = Env::with_parent(&env_1);
    /// let r#true = T![abs "t", T![abs "f", T![var "t"]]];
    /// env_2.insert_variable("true", r#true.clone());
    /// assert_eq!(env_2.get_db_index("id"), Some(1));
    /// assert_eq!(env_2.get_db_index("true"), Some(0));
    ///
    /// assert_eq!(env_2.get_db_index("y"), None);
    /// ```
    pub fn get_db_index(&self, name: impl Into<Symbol>) -> Option<usize> {
        self.get_db_index_(name.into(), 0)
    }

    fn get_db_index_(&self, name: Symbol, rec_level: usize) -> Option<usize> {
        self.context
            .get(&name)
            .map(|idx| idx + rec_level)
            .or_else(|| {
                self.parent
                    .and_then(|p| p.get_db_index_(name, rec_level + self.context.len()))
            })
    }
}

pub fn base_env() -> Env<'static> {
    match base_env_() {
        Ok(b) => b,
        Err(e) => {
            error!("{}", e);
            std::process::exit(1);
        }
    }
}

fn base_env_() -> Result<Env<'static>> {
    use crate::parser::parse;

    let mut env = Env::new();

    macro_rules! p {
        ($name:expr, $input:expr, $env:expr) => {
            let t = parse($input)?;
            rm_names(&t, &$env)?;
            $env.insert_variable($name, t);
        };
    }

    p!("true", "λt.λf.t", env);
    p!("false", "λt.λf.f", env);
    p!("not", "λb. b false true", env);
    p!("and", "λb.λc. b c false", env);
    p!("or", "λb.λc. b true c", env);
    p!("if", "λl.λm.λn. l m n", env);
    p!("pair", "λf.λs.λb. b f s", env);
    p!("first", "λp. p true", env);
    p!("second", "λp. p false", env);

    p!("c0", "λs.λz.z", env);
    p!("c1", "λs.λz.s z", env);
    p!("c2", "λs.λz.s (s z)", env);
    p!("c3", "λs.λz.s (s (s z))", env);

    p!("succ", "λn.λs.λz.s (n s z)", env);
    p!("plus", "λm.λn.λs.λz.m s (n s z)", env);
    p!("times", "λm.λn.m (plus n) c0", env);
    p!("iszero", "λm.m (λx.false) true", env);

    p!("zz", "pair c0 c0", env);
    p!("ss", "λp.pair (second p) (plus c1 (second p))", env);
    p!("pred", "λm. first (m ss zz)", env);

    p!("equalb", "λp.λq.p q (not q)", env);

    Ok(env)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Term, T};
    use std::rc::Rc;

    #[test]
    fn test_env() -> Result<()> {
        let mut env = Env::new();
        assert_eq!(env.get("id"), None);

        let id = T![abs "x", T![var "x", 0]];
        env.insert_variable("id", id.clone());
        assert_eq!(env.get("id"), Some(id.clone()));

        let tru = T![abs "t", T![abs "f", T![var "t", 1]]];
        env.insert_variable("true", tru.clone());
        assert_eq!(env.get("true"), Some(tru.clone()));
        assert_eq!(env.get("id"), Some(id.clone()));

        let mut id_env = Env::with_parent(&env);
        id_env.insert_local("x");
        assert_eq!(id_env.get("x"), None);
        assert_eq!(id_env.get_db_index("x"), Some(0));
        assert_eq!(id_env.get_db_index("id"), Some(1));
        assert_eq!(id_env.get_db_index("true"), Some(2));
        assert_eq!(id_env.get("id"), Some(id));
        assert_eq!(id_env.get("true"), Some(tru.clone()));

        let mut id_env_2 = Env::with_parent(&env);
        id_env_2.insert_local("id");
        assert_eq!(id_env_2.get("id"), None);
        assert_eq!(id_env_2.get_db_index("id"), Some(0));
        assert_eq!(id_env_2.get_db_index("true"), Some(2));
        assert_eq!(id_env_2.get("true"), Some(tru));

        Ok(())
    }
}
