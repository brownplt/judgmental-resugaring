use std::collections::HashMap;

use fresh::Atom;
use term::Term;
use term::Term::{Hole, Value, Var, Stx};
use tipe::Tipe;


pub struct Subs<V, T> {
    term_mapping: HashMap<Atom, Term<V>>,
    tipe_mapping: HashMap<Atom, Tipe<T>>
}

pub fn unify<V, T>(s: &Term<V>, t: &Term<V>) -> Option<Subs<V, T>>
    where V : Clone + Eq, T : Clone
{
    let mut subs = Subs::new();
    if subs.unify_terms(s, t) {
        Some(subs)
    } else {
        None
    }
}

impl<V, T> Subs<V, T> where V : Clone, T : Clone {
    pub fn apply(&self, term: Term<V>) -> Term<V> {
        match term {
            Hole(atom) => {
                match self.term_mapping.get(&atom) {
                    None => Hole(atom),
                    Some(term) => term.clone() // TODO: Assume unique holes?
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

    fn new() -> Subs<V, T> {
        Subs{
            term_mapping: HashMap::new(),
            tipe_mapping: HashMap::new()
        }
    }

    fn insert_term(&mut self, atom: Atom, defn: &Term<V>) -> bool
        where V : Clone + Eq
    {
        match self.term_mapping.remove(&atom) {
            None => {
                self.term_mapping.insert(atom, defn.clone());
                true
            }
            Some(term) => {
                self.unify_terms(&term, defn)
            }
        }
    }

    fn unify_terms(&mut self, left: &Term<V>, right: &Term<V>) -> bool
        where V : Clone + Eq
    {
        match (left, right) {
            
            (&Hole(ref atom), term) => self.insert_term(atom.clone(), term),
            (term, &Hole(ref atom)) => self.insert_term(atom.clone(), term),
            
            (&Var(_),       &Value(_))     => false,
            (&Var(_),       &Stx(_, _, _)) => false,
            (&Value(_),     &Stx(_, _, _)) => false,
            (&Value(_),     &Var(_))       => false,
            (&Stx(_, _, _), &Var(_))       => false,
            (&Stx(_, _, _), &Value(_))     => false,
            
            (&Var(ref x),   &Var(ref y))   => x == y,
            (&Value(ref x), &Value(ref y)) => x == y,
            
            (&Stx(ref node1, ref subterms1, ref mark1),
             &Stx(ref node2, ref subterms2, ref mark2)) => {
                if node1 != node2 || mark1 != mark2 {
                    return false;
                }
                if subterms1.len() != subterms2.len() {
                    return false;
                }
                for (s, t) in subterms1.into_iter().zip(subterms2.into_iter()) {
                    if !self.unify_terms(s, t) {
                        return false;
                    }
                }
                true
            }
        }
    }
}
