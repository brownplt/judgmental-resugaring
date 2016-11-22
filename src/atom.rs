use std::hash::Hash;

pub type Name = String;

pub struct Atom {
    name: String,
    id: usize
}

impl PartialEq for Atom {
    fn eq(&self, other: &Atom) -> bool {
        self.id == other.id
    }
}

impl Eq for Atom {}

impl Hash for Atom {
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        self.id.hash(state)
    }
}

