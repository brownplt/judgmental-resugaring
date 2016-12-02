use std::fmt;

use term::Term;
use fresh::{Fresh, Freshable};
use unify::{unify, Substitute, Subs};

struct RewriteRule<V> {
    rule: Fresh<(Term<V>, Term<V>)>
}

impl<V> RewriteRule<V> where V : Freshable + Eq {
    fn new(left: Term<V>, right: Term<V>) -> RewriteRule<V> {
        RewriteRule{
            rule: Fresh::new((left, right))
        }
    }
    
    fn apply(&self, term: &Term<V>) -> Option<Term<V>> {
        let (left, right) = self.rule.freshen();
        match unify(term, &left, Subs::empty()) {
            None => None,
            Some(subs) => Some(right.substitute(&subs))
        }
    }
}

pub struct RewriteRules<V> {
    rules: Vec<RewriteRule<V>>
}

impl<V> RewriteRules<V> where V : Freshable + Eq {
    fn new(rules: Vec<(Term<V>, Term<V>)>) -> RewriteRules<V> {
        let rules = rules.into_iter().map(|(left, right)| {
            RewriteRule::new(left, right)
        }).collect();
        RewriteRules{
            rules: rules
        }
    }
}

impl<V> fmt::Display for RewriteRule<V> where V : Freshable + fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (left, right) = self.rule.freshen();
        write!(f, "\nrule {}\n  => {};", left, right)
    }
}

impl<V> fmt::Display for RewriteRules<V> where V : Freshable + fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{{"));
        for rule in self.rules.iter() {
            let (left, right) = rule.rule.freshen();
            try!(write!(f, "\n    rule {}\n      => {}", left, right));
        }
        try!(write!(f, "}}"));
        Ok(())
    }
}
