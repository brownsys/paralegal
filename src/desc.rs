use std::hash::Hash;

use crate::{mir, serde, HashMap, HashSet, Symbol};

pub type Endpoint = Identifier;
pub type TypeDescriptor = Identifier;
pub type Function = Identifier;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Deserialize, serde::Serialize)]
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

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExceptionAnnotation {
    pub verification_hash: Option<VerificationHash>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct LabelAnnotation {
    #[serde(with = "crate::foreign_serializers::ser_sym")]
    pub label: Symbol,
    pub refinement: AnnotationRefinement,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Deserialize, serde::Serialize)]
pub struct AnnotationRefinement {
    on_argument: Vec<u16>,
    on_return: bool,
}

#[derive(Clone, serde::Deserialize, serde::Serialize)]
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

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, serde::Serialize, serde::Deserialize)]
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

#[derive(serde::Serialize, serde::Deserialize)]
pub struct ProgramDescription {
    pub controllers: HashMap<Endpoint, Ctrl>,
    pub annotations: HashMap<Identifier, (Vec<Annotation>, ObjectType)>,
}

impl ProgramDescription {
    pub fn all_sources(&self) -> HashSet<&DataSource> {
        self.controllers
            .values()
            .flat_map(|c| c.flow.0.keys().chain(c.types.0.keys()))
            .collect()
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
                    .flat_map(|v| v.iter().filter_map(DataSink::as_argument).map(|s| s.0))
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

#[derive(
    Hash, Eq, PartialEq, Ord, Debug, PartialOrd, Clone, serde::Serialize, serde::Deserialize, Copy,
)]
pub struct Identifier(#[serde(with = "crate::foreign_serializers::ser_sym")] Symbol);

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

impl<X: serde::Serialize, Y: serde::Serialize + std::hash::Hash + std::cmp::Eq> serde::Serialize
    for Relation<X, Y>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.iter().collect::<Vec<_>>().serialize(serializer)
    }
}

impl<
        'de,
        X: serde::Deserialize<'de> + std::hash::Hash + std::cmp::Eq,
        Y: serde::Deserialize<'de> + std::hash::Hash + std::cmp::Eq,
    > serde::Deserialize<'de> for Relation<X, Y>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        <Vec<_> as serde::Deserialize<'de>>::deserialize(deserializer)
            .map(|v| Self(v.into_iter().collect()))
    }
}

impl<X, Y> Relation<X, Y> {
    pub fn empty() -> Self {
        Relation(HashMap::new())
    }
}

#[derive(Hash, Eq, PartialEq, Ord, PartialOrd, Clone, serde::Serialize, serde::Deserialize)]
pub struct CallSite {
    #[serde(with = "crate::foreign_serializers::ser_loc")]
    pub location: mir::Location,
    pub called_from: Function,
    pub function: Function,
}

#[derive(Hash, Eq, PartialEq, Ord, PartialOrd, Clone, serde::Serialize, serde::Deserialize)]
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
    pub fn as_argument(&self) -> Option<usize> {
        match self {
            DataSource::Argument(a) => Some(*a),
            _ => None,
        }
    }
}

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, serde::Serialize, serde::Deserialize)]
pub enum DataSink {
    Argument { function: CallSite, arg_slot: usize },
    Return,
}

impl DataSink {
    pub fn as_argument(&self) -> Option<(&CallSite, usize)> {
        match self {
            DataSink::Argument { function, arg_slot } => Some((function, *arg_slot)),
            _ => None,
        }
    }
}

pub type CtrlTypes = Relation<DataSource, TypeDescriptor>;

#[derive(serde::Deserialize, serde::Serialize)]
pub struct Ctrl {
    pub flow: Relation<DataSource, DataSink>,
    pub types: CtrlTypes,
}

impl Ctrl {
    pub fn new() -> Self {
        Ctrl {
            flow: Relation::empty(),
            types: Relation::empty(),
        }
    }

    pub fn add_types<I: IntoIterator<Item = (DataSource, HashSet<TypeDescriptor>)>>(
        &mut self,
        i: I,
    ) {
        i.into_iter().for_each(|(ident, set)| {
            self.types
                .0
                .entry(ident)
                .or_insert_with(|| HashSet::new())
                .extend(set.into_iter())
        })
    }

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
