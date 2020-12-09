use crate::term::{rm_names, LTerm};
use crate::Symbol;
use anyhow::Result;
use log::error;
use std::collections::HashMap;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TermWithIndex {
    /// de Bruijn index
    pub db_idx: usize,
    /// term
    pub term: LTerm,
}

/// Terms are stored along with their calculated de Bruijn index
#[derive(Debug, Default)]
pub struct Env<'a> {
    context: HashMap<Symbol, TermWithIndex>,
    vars: Vec<LTerm>,
    parent: Option<&'a Env<'a>>,
}

impl<'a> Env<'a> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_parent(parent: &'a Env<'a>) -> Self {
        Self {
            parent: Some(parent),
            vars: Vec::with_capacity(1),
            // Every lambda is only allowed to have one variable
            // Only the root may have multiple.
            context: HashMap::with_capacity(1),
        }
    }

    pub fn get_from_db_index(&self, s: usize) -> Option<LTerm> {
        self.vars.get(s).cloned().or_else(|| {
            self.parent
                .and_then(|p| p.get_from_db_index(s - std::cmp::min(self.vars.len(), 1)))
        })
    }

    pub fn get(&self, s: impl Into<Symbol>) -> Option<LTerm> {
        let s = s.into();
        self.context
            .get(&s)
            // Term is a Rc, so cloning it is cheap
            .map(|ti| ti.term.clone())
            .or_else(|| self.parent.and_then(|p| p.get(s)))
    }

    pub fn insert(&mut self, k: impl Into<Symbol>, t: LTerm) {
        let db_idx = self.context.len();
        self.context.insert(
            k.into(),
            TermWithIndex {
                db_idx,
                term: t.clone(),
            },
        );
        self.vars.push(t);
    }

    /// Get the term pointed to by `name` with the calculated de Bruijn index.
    ///
    /// The index is calculated by the depth of the search + the original db_idx.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use lc::env::{Env, TermWithIndex};
    /// use lc::{T, Term};
    /// use std::rc::Rc;
    ///
    /// let mut env_1 = Env::new();
    /// let id = T![abs "x", T![var "x"]];
    /// env_1.insert("id", id.clone());
    /// assert_eq!(
    ///     env_1.get_with_calculated_db_index("id"),
    ///     Some(TermWithIndex { db_idx: 0, term: id.clone() })
    /// );
    ///
    /// let mut env_2 = Env::with_parent(&env_1);
    /// let r#true = T![abs "t", T![abs "f", T![var "t"]]];
    /// env_2.insert("true", r#true.clone());
    /// assert_eq!(
    ///     env_2.get_with_calculated_db_index("id"),
    ///     Some(TermWithIndex { db_idx: 1, term: id })
    /// );
    /// assert_eq!(
    ///     env_2.get_with_calculated_db_index("true"),
    ///     Some(TermWithIndex { db_idx: 0, term: r#true })
    /// );
    /// ```
    pub fn get_with_calculated_db_index(&self, name: impl Into<Symbol>) -> Option<TermWithIndex> {
        self.get_with_calculated_db_index_(name.into(), 0)
    }

    fn get_with_calculated_db_index_(
        &self,
        name: Symbol,
        rec_level: usize,
    ) -> Option<TermWithIndex> {
        self.context
            .get(&name)
            .map(|ti| TermWithIndex {
                db_idx: rec_level + ti.db_idx,
                term: ti.term.clone(),
            })
            .or_else(|| {
                self.parent
                    .and_then(|p| p.get_with_calculated_db_index_(name, rec_level + 1))
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
            $env.insert($name, t);
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
