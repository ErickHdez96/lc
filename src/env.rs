use crate::Symbol;
use crate::{term::LTerm, Error, ErrorKind};
use crate::{types::LTy, Span};
use std::collections::HashMap;

use std::rc::Rc;

macro_rules! error {
    ($msg:expr, $($arg:expr),*; $span:expr) => {
        Error::new(format!($msg, $($arg),*), $span, ErrorKind::Name)
    };
    ($msg:expr; $span:expr) => {
        error!($msg,;$span)
    };
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Default)]
pub struct TyEnv<'a> {
    types: HashMap<Symbol, LTy>,
    parent: Option<&'a TyEnv<'a>>,
}

impl<'a> TyEnv<'a> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_parent(parent: &'a TyEnv<'a>) -> Self {
        Self {
            types: HashMap::new(),
            parent: Some(parent),
        }
    }

    pub fn get(&self, s: impl Into<Symbol>) -> Option<LTy> {
        let s = s.into();
        self.types
            .get(&s)
            .map(Rc::clone)
            .or_else(|| self.parent.and_then(|p| p.get(s)))
    }

    pub fn insert(&mut self, s: impl Into<Symbol>, ty: &LTy) -> Result<()> {
        let s = s.into();
        if self.types.get(&s).is_some() {
            Err(error!("Type `{}` already bound", s; ty.span))
        } else {
            self.types.insert(s, Rc::clone(ty));
            Ok(())
        }
    }
}

#[derive(Debug)]
struct EnvTerm {
    index: usize,
    term: Option<LTerm>,
    ty: Option<LTy>,
}

#[derive(Debug, Default)]
pub struct Env<'a> {
    context: HashMap<Symbol, EnvTerm>,
    names: Vec<Symbol>,
    parent: Option<&'a Env<'a>>,
}

impl<'a> Env<'a> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_parent(parent: &'a Env<'a>) -> Self {
        Self {
            parent: Some(parent),
            names: Vec::with_capacity(1),
            // Every lambda is only allowed to have one variable
            // Only the root may have multiple.
            context: HashMap::with_capacity(1),
        }
    }

    pub(crate) fn insert_symbol(&mut self, s: impl Into<Symbol>, s_span: Span) -> Result<()> {
        let s = s.into();
        if self.context.get(&s).is_some() {
            Err(error!("Variable `{}` already bound", s; s_span))
        } else {
            self.insert_if_not_exists(s);
            Ok(())
        }
    }

    pub(crate) fn insert_type(&mut self, s: impl Into<Symbol>, ty: &LTy) -> Result<()> {
        let s = s.into();
        let val = self.insert_if_not_exists(Symbol::clone(&s));
        if val.ty.is_some() {
            Err(error!("Type `{}` already bound", s; ty.span))
        } else {
            val.ty = Some(Rc::clone(ty));
            Ok(())
        }
    }

    pub(crate) fn insert_term(&mut self, s: impl Into<Symbol>, term: &LTerm) -> Result<()> {
        let s = s.into();
        let val = self.insert_if_not_exists(Symbol::clone(&s));
        if val.term.is_some() {
            Err(error!("Variable `{}` already bound", s; term.span))
        } else {
            val.term = Some(Rc::clone(term));
            Ok(())
        }
    }

    fn insert_if_not_exists(&mut self, s: Symbol) -> &mut EnvTerm {
        if !self.context.contains_key(&s) {
            self.names.push(Symbol::clone(&s));
        }
        let index = self.context.len();
        self.context.entry(s).or_insert(EnvTerm {
            index,
            term: None,
            ty: None,
        })
    }

    pub fn get_type(&self, s: impl Into<Symbol>) -> Option<LTy> {
        let s = s.into();
        match self.context.get(&s) {
            Some(val) => val.ty.as_ref().map(Rc::clone),
            None => self.parent.and_then(|p| p.get_type(s)),
        }
    }

    pub fn get_type_from_index(&self, idx: usize) -> Option<LTy> {
        match self.names.get(idx) {
            Some(s) => self
                .context
                .get(s)
                .and_then(|t| t.ty.as_ref().map(Rc::clone)),
            None => self
                .parent
                .and_then(|p| p.get_type_from_index(idx - self.names.len())),
        }
    }

    pub fn get_term(&self, s: impl Into<Symbol>) -> Option<LTerm> {
        let s = s.into();
        match self.context.get(&s) {
            Some(val) => val.term.as_ref().map(Rc::clone),
            None => self.parent.and_then(|p| p.get_term(s)),
        }
    }

    pub fn get_term_from_index(&self, idx: usize) -> Option<LTerm> {
        match self.names.get(idx) {
            Some(s) => self
                .context
                .get(s)
                .and_then(|t| t.term.as_ref().map(Rc::clone)),
            None => self
                .parent
                .and_then(|p| p.get_term_from_index(idx - self.names.len())),
        }
    }

    /// Get the de Bruijn index of the term pointed to by `name`.
    ///
    /// The index is calculated by the depth of the search + the original db_idx.
    pub fn get_db_index(&self, name: impl Into<Symbol>) -> Option<usize> {
        self.get_db_index_(name.into(), 0)
    }

    fn get_db_index_(&self, name: Symbol, rec_level: usize) -> Option<usize> {
        self.context
            .get(&name)
            .map(|env_term| env_term.index + rec_level)
            .or_else(|| {
                self.parent
                    .and_then(|p| p.get_db_index_(name, rec_level + self.context.len()))
            })
    }

    pub fn get_name_from_db_index(&self, s: usize) -> Option<Symbol> {
        self.names.get(s).cloned().or_else(|| {
            self.parent.and_then(|p| {
                s.checked_sub(std::cmp::max(self.names.len(), 1))
                    .and_then(|s| p.get_name_from_db_index(s))
            })
        })
    }

    pub(crate) fn remove_symbol(&mut self, s: impl Into<Symbol>) {
        let s = s.into();
        if let Some(t) = self.context.get(&s) {
            self.names.remove(t.index);
            self.context.remove(&s);
        }
    }
}

pub fn base_env() -> (Env<'static>, TyEnv<'static>) {
    match base_env_() {
        Ok(b) => b,
        Err(e) => {
            log::error!("{}", e);
            std::process::exit(1);
        }
    }
}

fn base_env_() -> std::result::Result<(Env<'static>, TyEnv<'static>), Box<dyn std::error::Error>> {
    use crate::parser::parse;
    use crate::term::eval;
    let lc_std = include_str!("../std.lc");
    let mut env = Env::new();
    let mut tyenv = TyEnv::new();

    eval(&parse(lc_std, &mut env)?, &mut env, &mut tyenv)?;
    Ok((env, tyenv))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        parser::parse,
        types::{type_of, Ty, TyKind},
        Span,
    };
    use std::rc::Rc;

    #[test]
    fn test_env() -> Result<()> {
        let mut env = Env::new();
        let mut tyenv = TyEnv::new();
        let bool_ty = Rc::new(Ty {
            kind: TyKind::Bool,
            span: Span::new(0, 1),
        });
        assert_eq!(env.get_term("id"), None);

        let id = parse("λx:Bool.x", &mut env)?;
        let id_ty = type_of(&id, &mut env, &mut tyenv)?;
        env.insert_term("id", &id)?;
        env.insert_type("id", &id_ty)?;
        assert_eq!(env.get_term("id"), Some(id.clone()));

        let tru = parse("λt:Bool.λf:Bool.t", &mut env)?;
        let tru_ty = type_of(&tru, &mut env, &mut tyenv)?;
        env.insert_term("true", &tru)?;
        env.insert_type("true", &tru_ty)?;
        assert_eq!(env.get_term("true"), Some(tru.clone()));
        assert_eq!(env.get_term("id"), Some(id.clone()));

        let mut id_env = Env::with_parent(&env);
        id_env.insert_type("x", &bool_ty)?;
        assert_eq!(id_env.get_db_index("x"), Some(0));
        assert_eq!(id_env.get_db_index("id"), Some(1));
        assert_eq!(id_env.get_db_index("true"), Some(2));
        assert_eq!(id_env.get_term("id"), Some(id));
        assert_eq!(id_env.get_term("true"), Some(tru.clone()));

        let mut id_env_2 = Env::with_parent(&env);
        id_env_2.insert_type("id", &bool_ty)?;
        assert_eq!(id_env_2.get_db_index("id"), Some(0));
        assert_eq!(id_env_2.get_db_index("true"), Some(2));
        assert_eq!(id_env_2.get_term("true"), Some(tru));

        Ok(())
    }
}
