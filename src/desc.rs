use crate::{HashMap, HashSet};

pub type Endpoint = Identifier;

pub struct ProgramDescription {
    pub d: HashMap<Endpoint, Ctrl>,
}

impl ProgramDescription {
    pub fn empty() -> Self {
        ProgramDescription { d: HashMap::new() }
    }
}

impl ProgramDescription {
    pub fn all_arguments(&self) -> HashSet<&Identifier> {
        self.d
            .values()
            .flat_map(|ctrl| ctrl.flow.0.keys())
            .collect()
    }
    pub fn all_sinks(&self) -> HashSet<&DataSink> {
        self.d
            .values()
            .flat_map(|ctrl| ctrl.flow.0.values().flat_map(|v| v.iter()))
            .collect()
    }
}

#[derive(Hash, Eq, PartialEq, Ord, Debug, PartialOrd, Clone)]
pub struct Identifier(String);

impl Identifier {
    pub fn new(s: String) -> Self {
        Identifier(s)
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.0.fmt(f)
    }
}

pub struct Relation<X, Y>(pub HashMap<X, HashSet<Y>>);

impl<X, Y> Relation<X, Y> {
    pub fn empty() -> Self {
        Relation(HashMap::new())
    }
}

pub type DataSource = Identifier;

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DataSink {
    pub function: Identifier,
    pub arg_slot: usize,
}

pub struct Ctrl {
    pub flow: Relation<DataSource, DataSink>,
    pub witnesses: HashSet<Identifier>,
    pub sensitive: HashSet<Identifier>,
}

impl Ctrl {
    pub fn empty() -> Self {
        Ctrl {
            flow: Relation::empty(),
            witnesses: HashSet::new(),
            sensitive: HashSet::new(),
        }
    }
    pub fn add(&mut self, from: &DataSource, to: DataSink) {
        let m = &mut self.flow.0;
        if let Some(e) = m.get_mut(from) {
            e.insert(to);
        } else {
            m.insert(from.clone(), std::iter::once(to).collect());
        }
    }
}
