use std::fmt;

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
pub enum Term<C> {
    Hole(Name),
    Const(C),
    Var(Variable),
    Stx(Node, Vec<Term<C>>, Mark)
}

impl<C> fmt::Display for Term<C> where C : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Hole(ref hole) => write!(f, "{}", hole),
            &Const(ref c) => c.fmt(f),
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
