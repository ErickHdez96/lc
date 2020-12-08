use crate::term::LTerm;
use crate::Symbol;
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
    parent: Option<&'a Env<'a>>,
}

impl<'a> Env<'a> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_parent(parent: &'a Env<'a>) -> Self {
        Self {
            parent: Some(parent),
            // Every lambda is only allowed to have one variable
            // Only the root may have multiple.
            context: HashMap::with_capacity(1),
        }
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
        self.context
            .insert(k.into(), TermWithIndex { db_idx, term: t });
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
