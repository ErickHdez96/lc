use crate::term::LTerm;
use crate::Symbol;
use std::collections::HashMap;

#[derive(Debug, Default)]
pub struct Env<'a> {
    context: HashMap<Symbol, LTerm>,
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
            .cloned()
            .or_else(|| self.parent.and_then(|p| p.get(s)))
    }

    pub fn insert(&mut self, k: impl Into<Symbol>, t: LTerm) {
        self.context.insert(k.into(), t);
    }
}
