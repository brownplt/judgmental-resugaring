use std::fmt;
use std::collections::HashSet;

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
    Hole(Atom),
    Value(V),
    Var(Variable),
    Stx(Node, Vec<Term<V>>, Mark)
}

impl<V> fresh::Freshable for Term<V> where V : fresh::Freshable {
    fn freshen(&mut self, f: &mut fresh::Freshener) {
        match self {
            &mut Hole(ref mut atom) => atom.freshen(f),
            &mut Value(ref mut v)   => v.freshen(f),
            &mut Var(_)             => (), // TODO: Freshen?
            &mut Stx(_, ref mut subterms, _) => {
                for subterm in subterms.iter_mut() {
                    subterm.freshen(f);
                }
            }
        }
    }
}

impl<V> fmt::Display for Term<V> where V : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Hole(ref hole) => write!(f, "{}", hole),
            &Value(ref v) => v.fmt(f),
            &Var(ref var) => var.fmt(f),
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
        }
    }
}
