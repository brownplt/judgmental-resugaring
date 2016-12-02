use std::fmt;

use fresh::{Fresh, Freshable, Freshener};
use term::Term;
use unify::Subs;
use unify::{unify, Substitute};

#[derive(Clone)]
struct RuleData<V> {
    premises: Vec<Term<V>>,
    conclusion: Term<V>
}

pub struct Rule<V> {
    rule: Fresh<RuleData<V>>
}

pub struct Rules<V> {
    rules: Vec<Rule<V>>
}

// Invariant: antecedents.is_empty() iff conclusion.is_atomic()
#[derive(Clone)]
pub struct Derivation<V> {
    conclusion: Term<V>,
    antecedents: Vec<Derivation<V>>
}

impl<V> Freshable for RuleData<V> where V : Clone {
    fn freshen(&mut self, f: &mut Freshener) {
        for ref mut term in self.premises.iter_mut() {
            term.freshen(f);
        }
        self.conclusion.freshen(f);
    }
}

impl<V> Rule<V> where V : Clone + Eq {
    fn new(premises: Vec<Term<V>>, conclusion: Term<V>) -> Rule<V> {
        Rule{
            rule: Fresh::new(RuleData{
                premises: premises,
                conclusion: conclusion
            })
        }
    }

    fn apply(&self, term: &Term<V>, subs: Subs<V>)
             -> Option<(Subs<V>, Vec<Term<V>>)> {
        let mut rule = self.rule.freshen();
        match unify(&rule.conclusion, term, subs) {
            None => None,
            Some(subs) => {
                rule.premises = rule.premises.into_iter()
                    .map(|t| t.substitute(&subs))
                    .collect();
                Some((subs, rule.premises))
            }
        }
    }
}

impl<V> Derivation<V> {
    fn new(antecedents: Vec<Derivation<V>>, conclusion: Term<V>) -> Derivation<V> {
        Derivation{
            antecedents: antecedents,
            conclusion:  conclusion
        }
    }

    fn premises(&self) -> Vec<&Term<V>> {
       fn push_premises<'a, V>(deriv: &'a Derivation<V>,
                            premises: &mut Vec<&'a Term<V>>) {
           for antecedent in deriv.antecedents.iter() {
               push_premises(antecedent, premises);
           }
           if deriv.antecedents.is_empty() {
               premises.push(&deriv.conclusion);
           }
       }
        let mut premises = vec!();
        push_premises(self, &mut premises);
        premises
    }
}

impl<V> Substitute<V> for Derivation<V> where V : Clone {
    fn substitute(mut self, subs: &Subs<V>) -> Derivation<V> {
        self.conclusion = self.conclusion.substitute(subs);
        self.antecedents = self.antecedents.into_iter()
            .map(|t| t.substitute(subs))
            .collect();
        self
    }
}

fn derive<V>(rules: &Rules<V>, term: &Term<V>, subs: &Subs<V>)
             -> Vec<(Subs<V>, Derivation<V>)> where V : Clone + Eq {
    if term.is_atomic() {
        let deriv = Derivation::new(vec!(), term.clone());
        return vec!((subs.clone(), deriv))
    }
    let mut results = vec!();
    for (subs, antecedents) in rules.apply(term, subs) {
        for (subs, mut antecedents) in derive_seq(rules, &antecedents[..], &subs) {
            antecedents.reverse();
            let term = term.clone().substitute(&subs);
            let deriv = Derivation::new(antecedents, term);
            results.push((subs, deriv));
        }
    }
    results
}

fn derive_seq<V>(rules: &Rules<V>, terms: &[Term<V>], subs: &Subs<V>)
                 -> Vec<(Subs<V>, Vec<Derivation<V>>)> where V : Clone + Eq {
    if terms.is_empty() {
        return vec!((subs.clone(), vec!()));
    }
    let term = &terms[0];
    let terms = &terms[1..];
    let mut results = vec!();
    for (subs, deriv) in derive(rules, term, subs) {
        for (subs, mut derivs) in derive_seq(rules, terms, &subs) {
            derivs.push(deriv.clone());
            results.push((subs, derivs));
        }
    }
    results
}

impl<V> Rules<V> where V : Clone + Eq {
    fn apply(&self, term: &Term<V>, subs: &Subs<V>) -> Vec<(Subs<V>, Vec<Term<V>>)> {
        self.rules.iter().filter_map(|r| r.apply(term, subs.clone())).collect()
    }

    fn derive(&self, term: Term<V>) -> Vec<Derivation<V>> {
        let mut results = vec!();
        let derivations = derive(self, &term, &Subs::empty());
        for (_, deriv) in derivations.into_iter() {
            results.push(deriv);
        }
        results
    }
}


/* Printing */

impl<V> fmt::Display for RuleData<V> where V : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "rule "));
        for (i, t) in self.premises.iter().enumerate() {
            try!(write!(f, "{}", t));
            if i + 1 != self.premises.len() {
                try!(write!(f, " & "));
            }
        }
        write!(f, " -> {}", self.conclusion)
    }
}

impl<V> Derivation<V> where V : fmt::Display {
    fn fmt_indent(&self, f: &mut fmt::Formatter, indentation: usize) -> fmt::Result {
        for deriv in self.antecedents.iter() {
            deriv.fmt_indent(f, indentation + 1);
        }
        for _ in 0..indentation {
            try!(write!(f, "    "));
        }
        write!(f, "{}", self.conclusion)
    }
}

impl<V> fmt::Display for Derivation<V> where V : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "derivation"));
        self.fmt_indent(f, 1)
    }
}

impl<V> fmt::Display for Rule<V> where V : fmt::Display + Clone {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.rule.freshen())
    }
}
