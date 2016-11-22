use term::Term;
use fresh::Fresh;

pub struct RewriteRule<V> {
    rule: Fresh<(Term<V>, Term<V>)>
}

