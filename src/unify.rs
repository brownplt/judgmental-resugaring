use std::collections::HashMap;

use fresh::Atom;
use term::Term;
use term::Term::{Hole, Value, Var, Stx};

pub struct Subs<V> {
    mapping: HashMap<Atom, Term<V>>
}

pub fn unify<V>(s: Term<V>, t: Term<V>) -> Option<Subs<V>>
    where V : Clone + Eq
{
    let mut subs = Subs::new();
    if subs.unify(s, t) {
        Some(subs)
    } else {
        None
    }
}

impl<V> Subs<V> where V : Clone {
    pub fn apply(&self, term: Term<V>) -> Term<V> {
        match term {
            Hole(atom) => {
                match self.mapping.get(&atom) {
                    None => Hole(atom),
                    Some(term) => term.clone()
                }
            }
            Var(var) => Var(var),
            Value(c) => Value(c),
            Stx(node, subterms, mark) => {
                let subterms = subterms.into_iter().map(|term| {
                    self.apply(term)
                }).collect();
                Stx(node, subterms, mark)
            }
        }
    }

    fn new() -> Subs<V> {
        Subs{
            mapping: HashMap::new()
        }
    }

    fn insert(&mut self, atom: Atom, defn: Term<V>) -> bool
        where V : Clone + Eq
    {
        match self.mapping.remove(&atom) {
            None => {
                self.mapping.insert(atom, defn);
                true
            }
            Some(term) => {
                self.unify(term, defn)
            }
        }
    }

    fn unify(&mut self, left: Term<V>, right: Term<V>) -> bool
        where V : Clone + Eq
    {
        match (left, right) {
            
            (Hole(atom), term) => self.insert(atom, term),
            (term, Hole(atom)) => self.insert(atom, term),
            
            (Var(_),       Value(_))     => false,
            (Var(_),       Stx(_, _, _)) => false,
            (Value(_),     Stx(_, _, _)) => false,
            (Value(_),     Var(_))       => false,
            (Stx(_, _, _), Var(_))       => false,
            (Stx(_, _, _), Value(_))     => false,
            
            (Var(x), Var(y))     => x == y,
            (Value(x), Value(y)) => x == y,
            
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
