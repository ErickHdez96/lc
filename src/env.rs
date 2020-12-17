use crate::types::LTy;
use crate::Symbol;
use crate::{term::LTerm, Error};
use log::error;
use std::collections::HashMap;
use std::default;

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum IdxKind {
    Term,
    Type,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Idx {
    idx: usize,
    kind: IdxKind,
}

impl Idx {
    fn new(idx: usize, kind: IdxKind) -> Self {
        Self { idx, kind }
    }

    fn is_var(self) -> bool {
        self.kind == IdxKind::Term
    }
}

/// Terms are stored along with their calculated de Bruijn index
#[derive(Debug)]
pub struct Env<'a> {
    context: HashMap<Symbol, Idx>,
    vars: Vec<LTerm>,
    names: Vec<Symbol>,
    types: Vec<LTy>,
    parent: Option<&'a Env<'a>>,
}

impl<'a> default::Default for Env<'a> {
    fn default() -> Self {
        Self {
            context: HashMap::new(),
            vars: Vec::new(),
            names: Vec::new(),
            types: Vec::new(),
            parent: None,
        }
    }
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
            types: Vec::with_capacity(1),
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
        match self.context.get(&s) {
            Some(idx) if idx.is_var() => self.vars.get(idx.idx).cloned(),
            _ => self.parent.and_then(|p| p.get(s)),
        }
    }

    pub fn get_type(&self, idx: usize) -> Option<LTy> {
        self.types
            .get(idx)
            .cloned()
            .or_else(|| self.parent.and_then(|p| p.get_type(idx - self.types.len())))
    }

    pub fn get_type_from_symbol(&self, s: impl Into<Symbol>) -> Option<LTy> {
        let s = s.into();
        self.context
            .get(&s)
            .and_then(|i| self.types.get(i.idx))
            .cloned()
            .or_else(|| self.parent.and_then(|p| p.get_type_from_symbol(s)))
    }

    pub fn insert_local(&mut self, k: impl Into<Symbol>, ty: LTy) {
        let db_idx = self.context.len();
        let k = k.into();
        self.context.insert(k, Idx::new(db_idx, IdxKind::Term));
        self.names.push(k);
        self.types.push(ty);
    }

    pub fn insert_type(&mut self, k: impl Into<Symbol>, ty: LTy) {
        let db_idx = self.context.len();
        let k = k.into();
        self.context.insert(k, Idx::new(db_idx, IdxKind::Type));
        self.names.push(k);
        self.types.push(ty);
    }

    pub fn insert_let_term(&mut self, k: impl Into<Symbol>, t: LTerm) {
        let k = k.into();
        let db_idx = self.vars.len();
        self.context.insert(k, Idx::new(db_idx, IdxKind::Term));
        self.vars.push(t);
        self.names.push(k);
    }

    pub fn insert_variable(&mut self, k: impl Into<Symbol>, t: LTerm, ty: LTy) {
        let k = k.into();
        let db_idx = self.vars.len();
        self.context.insert(k, Idx::new(db_idx, IdxKind::Term));
        self.vars.push(t);
        self.names.push(k);
        self.types.push(ty);
    }

    pub fn insert_let_variable(&mut self, k: impl Into<Symbol>) {
        let db_idx = self.context.len();
        let k = k.into();
        self.context.insert(k, Idx::new(db_idx, IdxKind::Term));
        self.names.push(k);
    }

    pub fn get_immediate(&self, k: impl Into<Symbol>) -> Option<usize> {
        self.context.get(&k.into()).copied().map(|i| i.idx)
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
            .filter(|i| i.is_var())
            .map(|idx| idx.idx + rec_level)
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
    use crate::types::type_of;
    let mut env = Env::new();

    macro_rules! p {
        ($name:expr, $input:expr, $env:expr) => {
            let t = parse($input, &$env)?;
            let ty = type_of(&t, &mut $env)?;
            $env.insert_variable($name, t, ty);
        };
    }

    p!("not", "λb:Bool.if b then false else true", env);
    p!("and", "λb:Bool.λc:Bool.if b then c else false", env);
    p!("or", "λb:Bool.λc:Bool.if b then true else c", env);
    p!("eqb", "λb1:Bool.λb2:Bool.if b1 then b2 else not b2", env);
    p!("neqb", "λb1:Bool.λb2:Bool.if b1 then not b2 else b2", env);
    // p!("pair", "λf.λs.λb. b f s", env);
    // p!("first", "λp. p true", env);
    // p!("second", "λp. p false", env);

    // p!("plus", "λm.λn.λs.λz.m s (n s z)", env);
    // p!("times", "λm.λn.m (plus n) c0", env);

    Ok(env)
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
        let bool_ty = Rc::new(Ty {
            kind: TyKind::Bool,
            span: Span::new(0, 1),
        });
        assert_eq!(env.get("id"), None);

        let id = parse("λx:Bool.x", &env)?;
        let id_ty = type_of(&id, &mut env)?;
        env.insert_variable("id", id.clone(), id_ty);
        assert_eq!(env.get("id"), Some(id.clone()));

        let tru = parse("λt:Bool.λf:Bool.t", &env)?;
        let tru_ty = type_of(&tru, &mut env)?;
        env.insert_variable("true", tru.clone(), tru_ty);
        assert_eq!(env.get("true"), Some(tru.clone()));
        assert_eq!(env.get("id"), Some(id.clone()));

        let mut id_env = Env::with_parent(&env);
        id_env.insert_local("x", bool_ty.clone());
        assert_eq!(id_env.get("x"), None);
        assert_eq!(id_env.get_db_index("x"), Some(0));
        assert_eq!(id_env.get_db_index("id"), Some(1));
        assert_eq!(id_env.get_db_index("true"), Some(2));
        assert_eq!(id_env.get("id"), Some(id));
        assert_eq!(id_env.get("true"), Some(tru.clone()));

        let mut id_env_2 = Env::with_parent(&env);
        id_env_2.insert_local("id", bool_ty);
        assert_eq!(id_env_2.get("id"), None);
        assert_eq!(id_env_2.get_db_index("id"), Some(0));
        assert_eq!(id_env_2.get_db_index("true"), Some(2));
        assert_eq!(id_env_2.get("true"), Some(tru));

        Ok(())
    }
}
