use crate::{HashMap, HashSet};

pub type Endpoint = Identifier;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct SinkAnnotationPayload {
    pub leaks: Vec<u16>,
    pub scopes: Vec<u16>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Sink {
    pub ann: SinkAnnotationPayload,
    pub num_args: usize,
}

pub type Sinks = HashMap<Identifier, Sink>;

pub struct ProgramDescription {
    pub controllers: HashMap<Endpoint, Ctrl>,
    pub annotations: Sinks,
}

impl ProgramDescription {
    pub fn all_sources(&self) -> HashSet<&DataSource> {
        self.controllers
            .values()
            .flat_map(|c| c.flow.0.keys())
            .collect()
    }
    pub fn all_sinks(&self) -> HashSet<&DataSink> {
        self.controllers
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

#[derive(Hash, Eq, PartialEq, Ord, PartialOrd, Clone)]
pub enum DataSource {
    FunctionCall(Identifier),
    Argument(usize),
}

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
    pub fn add(&mut self, from: std::borrow::Cow<DataSource>, to: DataSink) {
        let m = &mut self.flow.0;
        if let Some(e) = m.get_mut(&from) {
            e.insert(to);
        } else {
            m.insert(from.into_owned(), std::iter::once(to).collect());
        }
    }
}
