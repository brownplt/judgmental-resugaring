use std::collections::HashMap;

use term::{Name, Term};
use term::Term::{Hole, Const, Var, Stx};

pub struct Subs<C> {
    mapping: HashMap<Name, Term<C>>
}

pub fn unify<C>(s: Term<C>, t: Term<C>) -> Option<Subs<C>>
    where C : Clone + Eq
{
    let mut subs = Subs::new();
    if subs.unify(s, t) {
        Some(subs)
    } else {
        None
    }
}

impl<C> Subs<C> where C : Clone {
    pub fn apply(&self, term: Term<C>) -> Term<C> {
        match term {
            Hole(name) => {
                match self.mapping.get(&name) {
                    None => Hole(name),
                    Some(term) => term.clone()
                }
            }
            Var(var) => Var(var),
            Const(c) => Const(c),
            Stx(node, subterms, mark) => {
                let subterms = subterms.into_iter().map(|term| {
                    self.apply(term)
                }).collect();
                Stx(node, subterms, mark)
            }
        }
    }

    fn new() -> Subs<C> {
        Subs{
            mapping: HashMap::new()
        }
    }

    fn insert(&mut self, name: Name, defn: Term<C>) -> bool
        where C : Clone + Eq
    {
        match self.mapping.remove(&name) {
            None => {
                self.mapping.insert(name, defn);
                true
            }
            Some(term) => {
                self.unify(term, defn)
            }
        }
    }

    fn unify(&mut self, left: Term<C>, right: Term<C>) -> bool
        where C : Clone + Eq
    {
        match (left, right) {
            
            (Hole(name), term) => self.insert(name, term),
            (term, Hole(name)) => self.insert(name, term),
            
            (Var(_),       Const(_))     => false,
            (Var(_),       Stx(_, _, _)) => false,
            (Const(_),     Stx(_, _, _)) => false,
            (Const(_),     Var(_))       => false,
            (Stx(_, _, _), Var(_))       => false,
            (Stx(_, _, _), Const(_))     => false,
            
            (Var(x), Var(y))     => x == y,
            (Const(x), Const(y)) => x == y,
            
            (Stx(node1, subterms1, mark1), Stx(node2, subterms2, mark2)) => {
                if node1 != node2 || mark1 != mark2 {
                    return false;
                }
                if subterms1.len() != subterms2.len() {
                    return false;
                }
                for (s, t) in subterms1.into_iter().zip(subterms2.into_iter()) {
                    if !self.unify(s, t) {
                        return false;
                    }
                }
                true
            }
        }
    }
}
