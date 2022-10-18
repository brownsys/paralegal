use crate::{mir, HashMap, HashSet, Symbol};

pub type Endpoint = Identifier;
pub type TypeDescriptor = Identifier;
pub type Function = Identifier;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Annotation {
    Label(LabelAnnotation),
    OType(Vec<TypeDescriptor>),
    Exception(ExceptionAnnotation),
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

    pub fn as_exception_annotation(&self) -> Option<&ExceptionAnnotation> {
        match self {
            Annotation::Exception(e) => Some(e),
            _ => None,
        }
    }
}

pub type VerificationHash = u128;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct ExceptionAnnotation {
    pub verification_hash: Option<VerificationHash>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct LabelAnnotation {
    pub label: Symbol,
    pub refinement: AnnotationRefinement,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct AnnotationRefinement {
    on_argument: Vec<u16>,
    on_return: bool,
}

#[derive(Clone)]
pub enum AnnotationRefinementKind {
    Argument(Vec<u16>),
    Return,
}

impl AnnotationRefinement {
    pub fn empty() -> Self {
        Self {
            on_argument: vec![],
            on_return: false,
        }
    }

    pub fn merge_kind(mut self, k: AnnotationRefinementKind) -> Result<Self, String> {
        match k {
            AnnotationRefinementKind::Argument(a) => {
                if self.on_argument.is_empty() {
                    self.on_argument = a;
                    Ok(self)
                } else {
                    Err(format!(
                        "Double argument annotation {:?} and {a:?}",
                        self.on_argument
                    ))
                }
            }
            AnnotationRefinementKind::Return => {
                if !self.on_return {
                    self.on_return = true;
                    Ok(self)
                } else {
                    Err(format!("Double on-return annotation"))
                }
            }
        }
    }

    pub fn on_argument(&self) -> &[u16] {
        &self.on_argument
    }

    pub fn on_return(&self) -> bool {
        self.on_return
    }

    pub fn on_self(&self) -> bool {
        self.on_argument.is_empty() && !self.on_return
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum ObjectType {
    Function(usize),
    Type,
    Other,
}

impl ObjectType {
    pub fn is_function(&self) -> Option<usize> {
        match self {
            ObjectType::Function(f) => Some(*f),
            _ => None,
        }
    }
    pub fn merge(&mut self, other: &Self) {
        if self != other {
            warn!(
                "Merging two different object types {:?} and {:?}!",
                self, other
            );
            match (self, other) {
                (ObjectType::Function(ref mut i), ObjectType::Function(j)) => {
                    if j > i {
                        *i = *j
                    }
                }
                (slf, other) => {
                    panic!("Cannot merge two different object types {slf:?} and {other:?}")
                }
            }
        }
    }
    pub fn is_type(&self) -> bool {
        matches!(self, ObjectType::Type)
    }
}

pub struct ProgramDescription {
    pub controllers: HashMap<Endpoint, Ctrl>,
    pub annotations: HashMap<Identifier, (Vec<Annotation>, ObjectType)>,
}

impl ProgramDescription {
    pub fn all_sources(&self) -> impl Iterator<Item = &DataSource> {
        self.controllers.values().flat_map(|c| c.flow.0.keys())
    }
    pub fn all_sinks(&self) -> HashSet<&DataSink> {
        self.controllers
            .values()
            .flat_map(|ctrl| ctrl.flow.0.values().flat_map(|v| v.iter()))
            .collect()
    }

    pub fn all_call_sites(&self) -> HashSet<&CallSite> {
        self.controllers
            .values()
            .flat_map(|ctrl| {
                ctrl.flow
                    .0
                    .values()
                    .flat_map(|v| v.iter().map(|s| &s.function))
                    .chain(ctrl.flow.0.keys().filter_map(|src| src.as_function_call()))
            })
            .collect()
    }

    pub fn all_functions(&self) -> HashSet<&Identifier> {
        self.all_call_sites()
            .into_iter()
            .map(|cs| &cs.function)
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
    pub fn from_str(s: &str) -> Self {
        Self::new(Symbol::intern(s))
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
pub struct CallSite {
    pub location: mir::Location,
    pub function: Function,
}

#[derive(Hash, Eq, PartialEq, Ord, PartialOrd, Clone)]
pub enum DataSource {
    FunctionCall(CallSite),
    Argument(usize),
}

impl DataSource {
    pub fn as_function_call(&self) -> Option<&CallSite> {
        match self {
            DataSource::FunctionCall(i) => Some(i),
            _ => None,
        }
    }
}

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DataSink {
    pub function: CallSite,
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
