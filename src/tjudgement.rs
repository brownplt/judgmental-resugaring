use std::fmt;
use std::collections::HashMap;

use fresh::Atom;
use term::Term;

pub struct TJudgement<V, T> {
    tenv: TEnv<T>,
    term: Term<V>,
    tipe: Tipe<T>
}

pub struct TEnv<T> {
    mapping: HashMap<Atom, Tipe<T>>
}

pub enum Tipe<T> {
    TVar(Atom),
    TConst(T)
}

impl<T> fmt::Display for Tipe<T> where T : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Tipe::TVar(ref atom)   => write!(f, "{}", atom),
            &Tipe::TConst(ref tipe) => write!(f, "{}", tipe)
        }
    }
}

impl<T> fmt::Display for TEnv<T> where T : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "Γ"));
        for (atom, ty) in self.mapping.iter() {
            try!(write!(f, ", {}:{}", atom, ty));
        }
        Ok(())
    }    
}

impl<V, T> fmt::Display for TJudgement<V, T>
    where V : fmt::Display, T : fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ⊢ {} : {}", self.tenv, self.term, self.tipe)
    }
}
