use crate::{HashMap, HashSet, Symbol};

pub type Endpoint = Identifier;
pub type TypeDescriptor = Identifier;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Annotation {
    Label(LabelAnnotation),
    OType(Vec<TypeDescriptor>),
}

impl Annotation {
    pub fn as_label_ann(&self) -> Option<&LabelAnnotation> {
        match self {
            Annotation::Label(l) => Some(l),
            _ => None,
        }
    }

    pub fn as_otype_ann(&self) -> Option<&[TypeDescriptor]> {
        match self {
            Annotation::OType(t) => Some(t),
            _ => None,
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct LabelAnnotation {
    pub label: Symbol,
    pub refinement: AnnotationRefinement,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum AnnotationRefinement {
    Argument(Vec<u16>),
    None,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ObjectType {
    Function(usize),
    Type,
}

impl ObjectType {
    pub fn is_function(&self) -> Option<usize> {
        match self {
            ObjectType::Function(f) => Some(*f),
            _ => None,
        }
    }
}

pub struct ProgramDescription {
    pub controllers: HashMap<Endpoint, Ctrl>,
    pub annotations: HashMap<Identifier, (Vec<Annotation>, ObjectType)>,
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
pub struct Identifier(Symbol);

impl Identifier {
    pub fn new(s: Symbol) -> Self {
        Identifier(s)
    }
    pub fn as_str(&self) -> &str {
        self.0.as_str()
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

pub type CtrlTypes = HashMap<DataSource, HashSet<TypeDescriptor>>;

pub struct Ctrl {
    pub flow: Relation<DataSource, DataSink>,
    pub types: CtrlTypes,
}

impl Ctrl {
    pub fn with_input_types(types: CtrlTypes) -> Self {
        Ctrl {
            flow: Relation::empty(),
            types,
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
