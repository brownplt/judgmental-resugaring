use std::collections::HashMap;

use fresh::Atom;
use term::Term;
use term::Term::{Const, MetaVar, Value, LitVar, Stx, Env};


#[derive(Clone)]
pub struct Subs<V> {
    term_mapping: HashMap<Atom, Term<V>>,
}

pub fn unify<V>(s: &Term<V>, t: &Term<V>, mut subs: Subs<V>) -> Option<Subs<V>>
    where V : Clone + Eq
{
    if subs.unify_terms(s, t) {
        Some(subs)
    } else {
        None
    }
}

pub trait Substitute<V> {
    fn substitute(self, subs: &Subs<V>) -> Self;
}

impl<V> Substitute<V> for Term<V> where V : Clone {
    fn substitute(self, subs: &Subs<V>) -> Term<V> {
        match self {
            MetaVar(atom) => {
                match subs.term_mapping.get(&atom) {
                    None => MetaVar(atom),
                    Some(term) => term.clone() // TODO: Assume unique consts?
                }
            }
            Const(atom) => Const(atom),
            LitVar(var) => LitVar(var),
            Value(c) => Value(c),
            Stx(node, subterms, mark) => {
                let subterms = subterms.into_iter().map(|term| {
                    term.substitute(subs)
                }).collect();
                Stx(node, subterms, mark)
            }
            Env(var, env) => {
                let env = env.into_iter().map(|(key, term)| {
                    (key, term.substitute(subs))
                }).collect();
                // TODO: Subs into env var?
                Env(var, env)
            }
        }
    }
}

impl<V> Subs<V> {
    pub fn empty() -> Subs<V> {
        Subs{
            term_mapping: HashMap::new()
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
            
            (&Const(ref atom), term) => self.insert_term(atom.clone(), term),
            (term, &Const(ref atom)) => self.insert_term(atom.clone(), term),
                        
            (&LitVar(ref x), &LitVar(ref y)) => x == y,
            (&Value(ref x),  &Value(ref y))  => x == y,
            
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

            (&Env(ref var1, ref env1),
             &Env(ref var2, ref env2)) => {
                if !self.insert_term(var1.clone(), &MetaVar(var2.clone())) {
                    return false;
                }
                panic!("NYI")
            }

            (_, _) => false
        }
    }
}
