use std::fmt;
use std::collections::HashMap;

use fresh;
use fresh::Atom;

use self::Variable::*;
use self::Term::*;
use self::Mark::*;

pub type Name = String;
pub type Node = String;

#[derive(Clone, PartialEq, Eq)]
pub enum Variable {
    Decl(Name),
    Refn(Name),
    Global(Name)
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Decl(ref name) => write!(f, "@{}", name),
            &Refn(ref name) => write!(f, "${}", name),
            &Global(ref name) => write!(f, "global${}", name)
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mark {
    Core,
    Surf
}

#[derive(Clone)]
pub enum Term<V> {
    Const(Atom),
    MetaVar(Atom),    // meta-language variable
    Value(V),
    LitVar(Variable), // object-language variable
    Stx(Node, Vec<Term<V>>, Mark),
    Env(Atom, HashMap<Atom, Term<V>>)
}

impl<V> Term<V> {
    pub fn is_atomic(&self) -> bool {
        match self {
            &Stx(_, ref subterms, _) => subterms.is_empty(),
            _ => false
        }
    }
}

impl<V> fresh::Freshable for Term<V> where V : Clone {
    fn freshen(&mut self, f: &mut fresh::Freshener) {
        match self {
            &mut Const(ref mut atom)   => atom.freshen(f),
            &mut MetaVar(ref mut atom) => atom.freshen(f),
            &mut Value(ref mut v)      => (),
            &mut LitVar(_)             => (), // TODO: Freshen?
            &mut Stx(_, ref mut subterms, _) => {
                for subterm in subterms.iter_mut() {
                    subterm.freshen(f);
                }
            }
            &mut Env(ref mut atom, ref mut map) => {
                atom.freshen(f);
                let drained: Vec<(Atom, Term<V>)> = map.drain().collect();
                for (mut atom, mut term) in drained {
                    atom.freshen(f);
                    term.freshen(f);
                    map.insert(atom, term);
                }
            }
        }
    }
}

impl<V> fmt::Display for Term<V> where V : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Const(ref atom) => write!(f, "'{}", atom),
            &MetaVar(ref var) => write!(f, "{}", var),
            &Value(ref v) => v.fmt(f),
            &LitVar(ref var) => var.fmt(f),
            &Stx(ref node, ref subterms, mark) => {
                match mark {
                    Core => try!(write!(f, "(")),
                    Surf => try!(write!(f, "["))
                }
                try!(write!(f, "{}", node));
                for subterm in subterms.iter() {
                    try!(write!(f, " {}", subterm));
                }
                match mark {
                    Core => write!(f, ")"),
                    Surf => write!(f, "]")
                }
            }
            &Env(ref var, ref env) => {
                try!(write!(f, "{{"));
                try!(write!(f, "{}", var));
                for (key, term) in env.iter() {
                    try!(write!(f, ", {}: {}", key, term));
                }
                try!(write!(f, "}}"));
                Ok(())
            }
        }
    }
}
