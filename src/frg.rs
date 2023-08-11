//! Forge serializers for data structures from [`desc`](crate::desc) based on
//! the [`pretty`] crate.
//!
//! A description of the Forge entities we emit and what they mean can be found
//! [here](https://www.notion.so/justus-adam/Using-Dataflow-0fb0b2bef50c40b1ba888d623c447e80#2a405f54559741ae9d17ec746a3c14f1)

extern crate pretty;

use std::hash::Hash;

use crate::{ir::IsGlobalLocation, utils::IntoDefId, HashSet, ModelCtrl, TyCtxt};
use pretty::{DocAllocator, DocBuilder, Pretty};

use crate::desc::{
    Annotation, CallSite, DataSink, DataSource, Identifier, ObjectType, ProgramDescription,
    Relation,
};

use self::name::Qualifier;

/// Extension trait to lay out a sequence of documents with [`DocAllocator::hardline`]s
/// in between.
trait DocLines<'a, A = ()>: DocAllocator<'a, A>
where
    A: 'a,
{
    #[inline]
    fn lines<I>(&'a self, docs: I) -> DocBuilder<'a, Self, A>
    where
        I: IntoIterator,
        I::Item: Pretty<'a, Self, A>,
        DocBuilder<'a, Self, A>: Clone,
    {
        self.intersperse(docs, self.hardline())
    }
}

impl<'a, T, A> DocLines<'a, A> for T
where
    T: DocAllocator<'a, A>,
    A: 'a,
{
}

/// Extension trait to lay out an iterator as a Forge relation.
///
/// Each element of the iterator a tuple of iterators `(left, right)` which are
/// then laid out like `(left.next() + left.next() + ...)->(right.next() +
/// right.next() + ...)`. And then the rows are laid out with `+` in between.
///
/// Importantly this tries to handle cases correctly where the iterators are
/// empty, in which case it emits `none` and not just empty parentheses (which
/// would be an error in Forge).
trait DocFrgRel<'a, A = ()>: DocAllocator<'a, A>
where
    A: 'a,
{
    #[inline]
    fn forge_relation_with_arity<I, LIter, RIter>(
        &'a self,
        arity: usize,
        rel: I,
    ) -> DocBuilder<'a, Self, A>
    where
        I: IntoIterator<Item = (LIter, RIter)>,
        LIter: IntoIterator,
        LIter::Item: Pretty<'a, Self, A>,
        RIter: IntoIterator,
        RIter::Item: Pretty<'a, Self, A>,
        DocBuilder<'a, Self, A>: Clone,
    {
        assert!(arity > 1);
        let mut prit = rel
            .into_iter()
            .filter_map(|(l, r)| {
                let mut pl = l.into_iter().peekable();
                let mut pr = r.into_iter().peekable();
                if pl.peek().is_some() && pr.peek().is_some() {
                    Some(
                        self.intersperse(pl, self.text(" + "))
                            .parens()
                            .append("->")
                            .append(self.intersperse(pr, self.text(" + ")).parens()),
                    )
                } else {
                    None
                }
            })
            .peekable();
        if prit.peek().is_some() {
            self.intersperse(prit, self.text(" +").append(self.hardline()))
        } else {
            self.intersperse(std::iter::repeat("none").take(arity), "->")
        }
    }

    #[inline]
    fn forge_relation<I, LIter, RIter>(&'a self, rel: I) -> DocBuilder<'a, Self, A>
    where
        I: IntoIterator<Item = (LIter, RIter)>,
        LIter: IntoIterator,
        LIter::Item: Pretty<'a, Self, A>,
        RIter: IntoIterator,
        RIter::Item: Pretty<'a, Self, A>,
        DocBuilder<'a, Self, A>: Clone,
    {
        self.forge_relation_with_arity(2, rel)
    }
}

impl<'a, T, A> DocFrgRel<'a, A> for T
where
    T: DocAllocator<'a, A>,
    A: 'a,
{
}

/// A serialization trait for Forge.
pub trait ToForge<'a, A, D>
where
    A: 'a,
    D: ?std::marker::Sized + DocAllocator<'a, A>,
{
    fn build_forge(self, alloc: &'a D) -> DocBuilder<'a, D, A>;
}

lazy_static! {
    /// Symbols that are used in forge and therefore cannot be an identifier so
    /// we have to escape them.
    static ref FORGE_RESERVED_SYMBOLS: HashSet<Identifier> = [
        "expect", "test", "implies", "is", "not", "some", "all", "sig", "pred", "no", "one", "sig",
        "open", "and", "abstract", "extends", "none", "set"
    ]
    .into_iter()
    .map(Identifier::new_intern)
    .collect();
}

impl<'a, A: 'a, D: DocAllocator<'a, A>> ToForge<'a, A, D> for Identifier {
    fn build_forge(self, alloc: &'a D) -> DocBuilder<'a, D, A> {
        alloc
            .text("`")
            .append(alloc.text(if FORGE_RESERVED_SYMBOLS.contains(&self) {
                "s__".to_string() + self.as_str()
            } else {
                self.as_str().to_owned()
            }))
    }
}

impl<'a, A: 'a, D: DocAllocator<'a, A>> ToForge<'a, A, D> for &'a Identifier {
    fn build_forge(self, alloc: &'a D) -> DocBuilder<'a, D, A> {
        (*self).build_forge(alloc)
    }
}

impl<'a, A: 'a + Clone, D: DocAllocator<'a, A>, X, Y> ToForge<'a, A, D> for &'a Relation<X, Y>
where
    D::Doc: Clone,
    &'a X: ToForge<'a, A, D>,
    &'a Y: ToForge<'a, A, D>,
{
    fn build_forge(self, alloc: &'a D) -> DocBuilder<'a, D, A> {
        alloc.forge_relation(self.0.iter().map(|(src, sinks)| {
            (
                std::iter::once(src.build_forge(alloc)),
                sinks.iter().map(|sink| sink.build_forge(alloc)),
            )
        }))
    }
}

impl<'a, A: 'a, D: DocAllocator<'a, A>> ToForge<'a, A, D> for &'a str {
    fn build_forge(self, alloc: &'a D) -> DocBuilder<'a, D, A> {
        alloc.text(self)
    }
}

/// Basically a decomposed version of `ToForge` for `DataSink` for the case
/// where you have its constituent parts but not a `DataSink`.
fn data_sink_as_forge<'b, A, D: DocAllocator<'b, A>>(
    alloc: &'b D,
    function: &'b CallSite,
    arg_slot: usize,
) -> DocBuilder<'b, D, A> {
    alloc
        .text("`arg")
        .append(alloc.as_string(arg_slot))
        .append(alloc.text("_"))
        .append(function.to_string())
}

impl<'a, A: 'a, D: DocAllocator<'a, A>> ToForge<'a, A, D> for &'a DataSink {
    fn build_forge(self, alloc: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            DataSink::Return => alloc.text("`Return"),
            DataSink::Argument { function, arg_slot } => {
                data_sink_as_forge(alloc, function, *arg_slot)
            }
        }
    }
}

impl<'a, A: 'a, D: DocAllocator<'a, A>, T> ToForge<'a, A, D> for &'a HashSet<T>
where
    &'a T: ToForge<'a, A, D>,
{
    fn build_forge(self, alloc: &'a D) -> DocBuilder<'a, D, A> {
        if self.is_empty() {
            alloc.text("none")
        } else {
            alloc.intersperse(self.iter().map(|w| w.build_forge(alloc)), "+")
        }
    }
}

fn call_site_as_forge<'b, A, D: DocAllocator<'b, A>>(
    alloc: &'b D,
    function: &'b CallSite,
) -> DocBuilder<'b, D, A> {
    alloc.text("`").append(function.to_string())
}

impl<'a, A: 'a, D: DocAllocator<'a, A>> ToForge<'a, A, D> for &'a CallSite {
    fn build_forge(self, alloc: &'a D) -> DocBuilder<'a, D, A> {
        call_site_as_forge(alloc, self)
    }
}

fn data_source_as_forge<'b, A, D: DocAllocator<'b, A>>(
    src: &'b DataSource,
    alloc: &'b D,
    ctrl: Identifier,
) -> DocBuilder<'b, D, A> {
    match src {
        DataSource::FunctionCall(f) => call_site_as_forge(alloc, f),
        DataSource::Argument(a) => FormalParameter {
            function: ctrl,
            position: *a as u16,
        }
        .build_forge(alloc),
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Hash, serde::Serialize, serde::Deserialize)]
pub enum Version {
    V1,
    V2,
}

impl std::str::FromStr for Version {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "v1" => Ok(Version::V1),
            "v2" => Ok(Version::V2),
            other => Err(format!("Unknown version number {other}")),
        }
    }
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Version::V1 => "v1",
            Version::V2 => "v2",
        })
    }
}

pub mod name {
    //! Constants for the names of the Forge entities (`sig`s and relations) we
    //! emit.

    pub const SRC: &str = "Src";
    /// Previously "Call"
    //pub const CALL_ARGUMENT_OUTPUT: &'static str = "FnOut";
    /// Previously "Fn"
    pub const CALL_SITE: &str = "CallSite";
    /// Previously "CallSite"
    pub const CALL_ARGUMENT: &str = "CallArgument";
    pub const RETURN: &str = "Return";
    pub const SINK: &str = "Sink";
    pub const FUNCTION: &str = "Function";
    pub const FUN_REL: &str = "function";
    pub const FORMAL_PARAMETER: &str = "FormalParameter";
    pub const FORMAL_PARAMETER_FUNCTION: &str = "fp_fun_rel";
    pub const FORMAL_PARAMETER_ANNOTATION: &str = "fp_ann";
    pub const CTRL: &str = "Ctrl";
    pub const FLOW: &str = "flow";
    pub const CTRL_FLOW: &str = "ctrl_flow";
    pub const FLOWS_PREDICATE: &str = "Flows";
    pub const OBJ: &str = "Object";
    pub const LABEL: &str = "Label";
    pub const LABELS_REL: &str = "labels";
    pub const TYPES: &str = "types";
    pub const TYPE: &str = "Type";
    pub const ARG_CALL_SITE: &str = "arg_call_site";
    //pub const RETURN_CALL_SITE: &'static str = "ret_call_site";
    pub const OTYPE_REL: &str = "otype";
    pub const EXCEPTIONS_LABEL: &str = "exception";
    pub const CTRL_CALLS: &str = "calls";

    pub enum Qualifier {
        Abstract,
        One,
        No,
    }

    use Qualifier::*;

    #[allow(clippy::type_complexity)]
    /// A description of the preamble of Forge `sig`s we always emit.
    ///
    /// These are in topological order, because the code generation just
    /// iterates over this vector and emits them in the same order as in
    /// this vector and Forge requires everything (e.g. an inherited `sig`)
    /// to be defined before being referenced.
    pub fn sigs(
        version: super::Version,
    ) -> Vec<(
        &'static str,
        Qualifier,
        Option<&'static str>,
        Vec<(&'static str, String)>,
    )> {
        use super::Version::*;
        fn set(i: &str) -> String {
            "set ".to_string() + i
        }
        fn one(i: &str) -> String {
            "one ".to_string() + i
        }
        fn arr(from: &str, to: &str) -> String {
            from.to_string() + "->" + to
        }
        let mut sigs = vec![
            (LABEL, Abstract, None, vec![]),
            (OBJ, Abstract, None, vec![(LABELS_REL, set(LABEL))]),
            (FUNCTION, No, Some(OBJ), vec![]),
            (
                SRC,
                Abstract,
                Some(OBJ),
                match version {
                    V1 => vec![],
                    V2 => vec![
                        (FLOW, set(SINK)),
                        (CTRL_FLOW, set(CALL_SITE)),
                        (TYPES, set(TYPE)),
                    ],
                },
            ),
        ];
        match version {
            V1 => sigs.push((
                FORMAL_PARAMETER,
                No,
                Some(SRC),
                vec![
                    (FORMAL_PARAMETER_FUNCTION, set(FUNCTION)),
                    (FORMAL_PARAMETER_ANNOTATION, set(&arr(FUNCTION, LABEL))),
                ],
            )),
            V2 => sigs.push((
                FORMAL_PARAMETER,
                No,
                Some(SRC),
                vec![(FORMAL_PARAMETER_FUNCTION, set(FUNCTION))],
            )),
        }
        sigs.extend([
            (SINK, Abstract, Some(OBJ), vec![]),
            (RETURN, One, Some(SINK), vec![]),
            (
                CALL_ARGUMENT,
                No,
                Some(SINK),
                vec![(ARG_CALL_SITE, one(CALL_SITE))],
            ),
            (TYPE, No, Some(OBJ), vec![(OTYPE_REL, set(TYPE))]),
            (CALL_SITE, No, Some(SRC), vec![(FUN_REL, one(FUNCTION))]),
        ]);
        match version {
            V1 => sigs.push((
                CTRL,
                No,
                Some(FUNCTION),
                vec![
                    (FLOW, set(&arr(SRC, SINK))),
                    (CTRL_FLOW, set(&arr(SRC, CALL_SITE))),
                    (TYPES, set(&arr(SRC, TYPE))),
                ],
            )),
            V2 => sigs.push((CTRL, No, Some(FUNCTION), vec![(CTRL_CALLS, set(CALL_SITE))])),
        }

        sigs
    }
}

/// Emits `one sig <inner> extends <parent> {}`
fn make_one_sig<'a, A: Clone + 'a, D: DocAllocator<'a, A>, I: Pretty<'a, D, A>>(
    alloc: &'a D,
    inner: I,
    parent: &'static str,
) -> DocBuilder<'a, D, A>
where
    D::Doc: Clone,
{
    alloc
        .text("one sig ")
        .append(inner)
        .append(" extends ")
        .append(parent)
        .append(" {}")
}

/// Emits `(h[0] + h[1] + ...)` but also handles the empty set correctly (by
/// emitting `none`).
fn hash_set_into_forge<'a, A: 'a, D: DocAllocator<'a, A>, T: ToForge<'a, A, D>>(
    h: HashSet<T>,
    alloc: &'a D,
) -> DocBuilder<'a, D, A> {
    if h.is_empty() {
        alloc.text("none")
    } else {
        alloc.intersperse(h.into_iter().map(|w| w.build_forge(alloc)), "+")
    }
}

fn hash_set_into_call_site_forge<'a, A: 'a, D: DocAllocator<'a, A>>(
    h: HashSet<&'a CallSite>,
    alloc: &'a D,
) -> DocBuilder<'a, D, A> {
    if h.is_empty() {
        alloc.text("none")
    } else {
        alloc.intersperse(h.into_iter().map(|w| call_site_as_forge(alloc, w)), "+")
    }
}

/// Emit `sig`s for everything in [`name::SIGS`](struct@name::SIGS)
fn make_forge_sigs<'a, A: 'a + Clone, D: DocAllocator<'a, A>>(
    version: Version,
    alloc: &'a D,
) -> DocBuilder<'a, D, A>
where
    D::Doc: Clone,
{
    alloc.lines(
        name::sigs(version)
            .into_iter()
            .map(|(name, qualifier, parent, fields)| {
                alloc
                    .text(match qualifier {
                        Qualifier::Abstract => "abstract sig ",
                        Qualifier::No => "sig ",
                        Qualifier::One => "one sig ",
                    })
                    .append(name)
                    .append(parent.map_or(alloc.nil(), |p| alloc.text(" extends ").append(p)))
                    .append(alloc.space())
                    .append(
                        if fields.is_empty() {
                            alloc.nil()
                        } else {
                            alloc.hardline().append(
                                alloc
                                    .intersperse(
                                        fields.into_iter().map(|(name, typ)| {
                                            alloc.text(name).append(": ").append(alloc.text(typ))
                                        }),
                                        alloc.text(",").append(alloc.hardline()),
                                    )
                                    .indent(4)
                                    .append(alloc.hardline()),
                            )
                        }
                        .braces(),
                    )
            }),
    )
}

#[derive(Hash, PartialEq, Eq)]
struct FormalParameter {
    function: Identifier,
    position: u16,
}

impl<'a, A: 'a, D: DocAllocator<'a, A>> ToForge<'a, A, D> for FormalParameter {
    fn build_forge(self, alloc: &'a D) -> DocBuilder<'a, D, A> {
        alloc
            .text("`fp")
            .append(alloc.as_string(self.position))
            .append("_")
            .append(self.function.as_str().to_string())
    }
}

impl ProgramDescription {
    /// Returns all labels in this program description, including the special
    /// [`name::EXCEPTIONS_LABEL`] label.
    fn used_labels(&self) -> HashSet<Identifier> {
        self.annotations
            .values()
            .flat_map(|v| v.0.iter())
            .filter_map(Annotation::as_label_ann)
            .map(|a| a.marker)
            .chain(std::iter::once(crate::Symbol::intern(
                name::EXCEPTIONS_LABEL,
            )))
            .map(Identifier::new)
            .collect()
    }

    fn all_formal_parameters(&self) -> HashSet<FormalParameter> {
        self.annotations
            .iter()
            .flat_map(|(function, (_, oj))| {
                if let ObjectType::Function(num) = oj {
                    Some(num)
                } else {
                    None
                }
                .into_iter()
                .flat_map(|l| {
                    (0..*l).map(|position| FormalParameter {
                        function: *function,
                        position: position as u16,
                    })
                })
            })
            .chain(self.controllers.iter().flat_map(|(&function, ctrl)| {
                ctrl.data_flow
                    .0
                    .keys()
                    .chain(ctrl.types.0.keys())
                    .chain(ctrl.ctrl_flow.0.keys())
                    .filter_map(|src| src.as_argument())
                    .map(move |position| FormalParameter {
                        function,
                        position: position as u16,
                    })
            }))
            .collect()
    }

    /// Creates a `sig` for every label.
    fn make_label_sigs<'a, A: Clone + 'a, D: DocAllocator<'a, A>>(
        &self,
        alloc: &'a D,
    ) -> DocBuilder<'a, D, A>
    where
        D::Doc: Clone,
    {
        alloc.lines(
            self.used_labels()
                .into_iter()
                .map(|s| make_one_sig(alloc, alloc.text(s.as_str().to_string()), name::LABEL)),
        )
    }

    /// Returns all types mentioned in this program description.
    fn all_types(&self) -> HashSet<&Identifier> {
        self.annotations
            .iter()
            .filter(|t| t.1 .1 == ObjectType::Type)
            .map(|t| t.0)
            .collect()
    }

    fn make_labels_relation<'a, A: Clone + 'a, D: DocAllocator<'a, A>>(
        &'a self,
        alloc: &'a D,
    ) -> DocBuilder<'a, D, A>
    where
        D::Doc: Clone,
    {
        alloc
            .forge_relation(self.annotations.iter().flat_map(|(id, (anns, _typ))| {
                // I've decided to do the more
                // complicated thing here which
                // restores the old behavior. Is
                // this the right thing to do?
                // Maybe, maybe not. Only time will
                // tell.
                //
                // The "old behavior" I am restoring is that if there is a label
                // `l` on function `f`, then what is actually emitted into forge
                // is `cs1_f->l + cs2_f->l`, i.e. the label is being attached to
                // each call site of the function in addition to the function
                // itself.
                // Part of why we choose this behavior is because there is no
                // call-site-independent representation for arguments, so the
                // label has to be attached to the call site argument.
                anns.iter()
                    .filter_map(Annotation::as_label_ann)
                    .map(move |a| {
                        (
                            if a.refinement.on_return() {
                                Some(self.all_sources_with_ctrl().into_iter().filter(|(_, s)| {
                                    s.as_function_call().map_or(false, |c| &c.function == id)
                                }))
                            } else {
                                None
                            }
                            .into_iter()
                            .flatten()
                            .map(|(ctrl, ds)| data_source_as_forge(ds, alloc, ctrl))
                            .chain(
                                self.all_sinks()
                                    .into_iter()
                                    .filter(|s| {
                                        matches!(
                                            s,
                                            DataSink::Argument{function, arg_slot} if
                                            &function.function == id
                                                && a.refinement
                                                    .on_argument()
                                                    .is_set(*arg_slot as u32)
                                        )
                                    })
                                    .map(|s| s.build_forge(alloc)),
                            )
                            .chain([id.build_forge(alloc)])
                            .chain(a.refinement.on_argument().into_iter_set_in_domain().map(
                                |slot| {
                                    FormalParameter {
                                        function: *id,
                                        position: slot as u16,
                                    }
                                    .build_forge(alloc)
                                },
                            ))
                            // This is necessary because otherwise captured variables escape
                            .collect::<Vec<_>>()
                            .into_iter(),
                            std::iter::once(Identifier::new(a.marker).build_forge(alloc)),
                        )
                    })
            }))
            .append(" +")
            .append(alloc.hardline())
            .append(
                alloc.forge_relation(self.annotations.iter().map(|(id, (anns, _))| {
                    (
                        anns.iter()
                            .filter_map(Annotation::as_exception_annotation)
                            .next()
                            .map(|_| id.build_forge(alloc))
                            .into_iter(),
                        std::iter::once(alloc.text(name::EXCEPTIONS_LABEL)),
                    )
                })),
            )
    }

    fn make_callsite_argument_relation<'a, A: 'a + Clone, D: DocAllocator<'a, A>>(
        &'a self,
        alloc: &'a D,
    ) -> DocBuilder<'a, D, A>
    where
        D::Doc: Clone,
    {
        alloc.forge_relation(self.all_sinks().into_iter().filter_map(|src| {
            src.as_argument().map(|(function, _)| {
                (
                    std::iter::once(src.build_forge(alloc)),
                    std::iter::once(call_site_as_forge(alloc, function)),
                )
            })
        }))
    }

    fn make_return_func_relation<'a, A: Clone + 'a, D: DocAllocator<'a, A>>(
        &'a self,
        alloc: &'a D,
    ) -> DocBuilder<'a, D, A>
    where
        D::Doc: Clone,
    {
        alloc.forge_relation(self.all_call_sites().into_iter().map(|src| {
            (
                std::iter::once(call_site_as_forge(alloc, src)),
                std::iter::once((&src.function).build_forge(alloc)),
            )
        }))
    }

    fn make_otype_relation<'a, A: 'a + Clone, D: DocAllocator<'a, A>>(
        &'a self,
        alloc: &'a D,
    ) -> DocBuilder<'a, D, A>
    where
        D::Doc: Clone,
    {
        alloc.forge_relation(self.annotations.iter().map(|(o, (anns, _))| {
            (
                std::iter::once(o.build_forge(alloc)),
                anns.iter()
                    .filter_map(Annotation::as_otype_ann)
                    .flat_map(|v| v.iter())
                    .map(|t| t.build_forge(alloc)),
            )
        }))
    }
    fn make_formal_param_relation<'a, A: 'a + Clone, D: DocAllocator<'a, A>>(
        &'a self,
        alloc: &'a D,
    ) -> DocBuilder<'a, D, A>
    where
        D::Doc: Clone,
    {
        alloc.forge_relation(self.all_formal_parameters().into_iter().map(|p| {
            let fn_forge = p.function.build_forge(alloc);
            (
                std::iter::once(p.build_forge(alloc)),
                std::iter::once(fn_forge),
            )
        }))
    }

    fn make_types_relation<'a, A: 'a, D: DocAllocator<'a, A>>(
        &'a self,
        alloc: &'a D,
        version: Version,
    ) -> DocBuilder<'a, D, A>
    where
        D::Doc: Clone,
        A: Clone,
    {
        match version {
            Version::V1 => alloc.forge_relation_with_arity(
                3,
                self.controllers.iter().map(|(e, ctrl)| {
                    (
                        std::iter::once(e.build_forge(alloc)),
                        std::iter::once(
                            alloc.hardline().append(
                                alloc
                                    .forge_relation(ctrl.types.0.iter().map(|(i, desc)| {
                                        (
                                            std::iter::once(data_source_as_forge(i, alloc, *e)),
                                            desc.iter().map(|t| t.build_forge(alloc)),
                                        )
                                    }))
                                    .indent(4),
                            ),
                        ),
                    )
                }),
            ),
            Version::V2 => alloc.forge_relation(self.controllers.iter().flat_map(|(e, ctrl)| {
                ctrl.types.0.iter().map(|(i, desc)| {
                    (
                        std::iter::once(data_source_as_forge(i, alloc, *e)),
                        desc.iter().map(|t| t.build_forge(alloc)),
                    )
                })
            })),
        }
    }
}

impl ProgramDescription {
    pub fn make_flow<'a, A: 'a + Clone, D: DocAllocator<'a, A>>(
        &'a self,
        alloc: &'a D,
        version: Version,
    ) -> DocBuilder<D, A>
    where
        D::Doc: Clone,
    {
        match version {
            Version::V1 => alloc.forge_relation_with_arity(
                3,
                self.controllers.iter().map(|(e, ctrl)| {
                    (
                        std::iter::once(e.build_forge(alloc)),
                        std::iter::once(
                            alloc.hardline().append(
                                //(&ctrl.data_flow).as_forge(alloc)
                                alloc
                                    .forge_relation(ctrl.data_flow.0.iter().map(
                                        |(source, sinks)| {
                                            (
                                                std::iter::once(data_source_as_forge(
                                                    source, alloc, *e,
                                                )),
                                                sinks.iter().map(|snk| snk.build_forge(alloc)),
                                            )
                                        },
                                    ))
                                    .indent(4),
                            ),
                        ),
                    )
                }),
            ),
            Version::V2 => alloc.forge_relation(self.controllers.iter().flat_map(|(e, ctrl)| {
                ctrl.data_flow.0.iter().map(|(src, snks)| {
                    (
                        std::iter::once(data_source_as_forge(src, alloc, *e)),
                        snks.iter().map(|snk| snk.build_forge(alloc)),
                    )
                })
            })),
        }
    }

    pub fn make_ctrl_flow<'a, A: 'a + Clone, D: DocAllocator<'a, A>>(
        &'a self,
        alloc: &'a D,
        version: Version,
    ) -> DocBuilder<D, A>
    where
        D::Doc: Clone,
    {
        match version {
            Version::V1 => alloc.forge_relation_with_arity(
                3,
                self.controllers.iter().map(|(e, ctrl)| {
                    (
                        std::iter::once(e.build_forge(alloc)),
                        std::iter::once(
                            alloc.hardline().append(
                                (alloc.forge_relation(ctrl.ctrl_flow.0.iter().map(
                                    |(src, sinks)| {
                                        (
                                            std::iter::once(data_source_as_forge(src, alloc, *e)),
                                            sinks
                                                .iter()
                                                .map(|sink| call_site_as_forge(alloc, sink)),
                                        )
                                    },
                                )))
                                .indent(4),
                            ),
                        ),
                    )
                }),
            ),
            Version::V2 => alloc.forge_relation(self.controllers.iter().flat_map(|(e, ctrl)| {
                ctrl.ctrl_flow.0.iter().map(|(src, snks)| {
                    (
                        std::iter::once(data_source_as_forge(src, alloc, *e)),
                        snks.iter().map(|snk| call_site_as_forge(alloc, snk)),
                    )
                })
            })),
        }
    }

    pub fn serialize_forge<'a, A: 'a + Clone, D: DocAllocator<'a, A>>(
        &'a self,
        alloc: &'a D,
        tcx: TyCtxt,
        model_ctrl: &ModelCtrl,
    ) -> DocBuilder<'a, D, A>
    where
        D::Doc: Clone,
    {
        let version = model_ctrl.model_version();
        alloc.lines([
            if model_ctrl.skip_sigs() {
                alloc.nil()
            } else {
                alloc.text("#lang forge")
            },
            alloc.nil(),
            alloc
                .text("/* This file is auto-generated by ")
                .append(crate_name!())
                .append(" version ")
                .append(crate_version!())
                .append(". */"),
            alloc.nil(),
            if model_ctrl.skip_sigs() {
                alloc.nil()
            } else {
                make_forge_sigs(version, alloc)
            },
            alloc.nil(),
            self.make_label_sigs(alloc),
            alloc.nil(),
            alloc.lines(
                self.all_call_sites().into_iter().map(|cs| {
                    let function = cs.location.innermost_function().into_def_id(tcx);

                    alloc.lines(
                        [
                            cs.build_forge(alloc).append(format!(" @ {}", cs.location)),
                            {
                                let did = cs.def_id.unwrap();
                                let base = alloc.text("   ").append(tcx.def_path_debug_str(did));
                                if tcx.def_kind(did).is_fn_like() {
                                    let sig = tcx.fn_sig(did).skip_binder().skip_binder();
                                    base.append(format!(" : {sig:?}"))
                                } else {
                                    base
                                }
                            },
                            alloc.text("   called from ").append(tcx.def_path_debug_str(function)),
                        ].into_iter().map(|l| alloc.text("// ").append(l)))
                })
            ),
            alloc.nil(),
            alloc
                .text("inst ")
                .append(name::FLOWS_PREDICATE)
                .append(" ")
                .append(
                    alloc
                        .lines([
                            alloc.nil(),
                            alloc
                                .text(name::LABEL)
                                .append(" = ")
                                .append(hash_set_into_forge(self.used_labels(), alloc)),
                            alloc.lines(self.used_labels().into_iter().map(|l| {
                                alloc
                                    .text(l.as_str().to_owned())
                                    .append(" = ")
                                    .append(l.build_forge(alloc))
                            })),
                            alloc.text(name::CALL_SITE).append(" = ").append(
                                hash_set_into_call_site_forge(self.all_call_sites(), alloc),
                            ),
                            // alloc.text(name::INPUT_ARGUMENT).append(" = ").append(
                            //     hash_set_into_forge(
                            //         self.all_sources()
                            //             .into_iter()
                            //             .filter(|s| s.as_argument().is_some())
                            //             .collect::<HashSet<_>>(),
                            //         alloc,
                            //     )
                            alloc
                                .text(name::FORMAL_PARAMETER)
                                .append(" = ")
                                .append(hash_set_into_forge(self.all_formal_parameters(), alloc)),

                            alloc
                                .text(name::SRC)
                                .append(" = ")
                                .append(hash_set_into_forge(
                                    [name::FORMAL_PARAMETER, name::CALL_SITE]
                                        .into_iter()
                                        .collect::<HashSet<_>>(),
                                    alloc,
                                )),
                            alloc.text(name::RETURN).append(" = `").append(name::RETURN),
                            alloc.text(name::CALL_ARGUMENT).append(" = ").append(
                                hash_set_into_forge(
                                    self.all_sinks()
                                        .iter()
                                        .filter_map(|ds| match ds {
                                            DataSink::Argument { .. } => Some(*ds),
                                            _ => None,
                                        })
                                        .collect(),
                                    alloc,
                                ),
                            ),
                            alloc
                                .text(name::SINK)
                                .append(" = ")
                                .append(hash_set_into_forge(
                                    [name::CALL_ARGUMENT, name::RETURN]
                                        .into_iter()
                                        .collect::<HashSet<_>>(),
                                    alloc,
                                )),
                            alloc
                                .text(name::TYPE)
                                .append(" = ")
                                .append(hash_set_into_forge(self.all_types(), alloc)),
                            alloc
                                .text(name::CTRL)
                                .append(" = ")
                                .append(hash_set_into_forge(
                                    self.controllers.keys().collect::<HashSet<_>>(),
                                    alloc,
                                )),
                            alloc
                                .text(name::FUNCTION)
                                .append(" = ")
                                .append(hash_set_into_forge(self.all_functions(), alloc))
                                .append(" + ")
                                .append(name::CTRL),
                            alloc
                                .text(name::OBJ)
                                .append(" = ")
                                .append(hash_set_into_forge(
                                    [
                                        name::FUNCTION,
                                        name::SRC,
                                        name::SINK,
                                        name::TYPE,
                                    ]
                                    .into_iter()
                                    .collect::<HashSet<_>>(),
                                    alloc,
                                )),
                            alloc.nil(),
                            alloc.text(name::FLOW).append(" = ").append(
                                alloc.hardline().append(
                                    self.make_flow(alloc, version)
                                        .indent(4),
                                ),
                            ),
                            alloc.text(name::CTRL_FLOW).append(" = ").append(
                                alloc.hardline().append(
                                        self.make_ctrl_flow(alloc, version)
                                        .indent(4),
                                ),
                            ),
                            alloc.text(name::TYPES).append(" = ").append(
                                alloc.hardline().append(
                                        self.make_types_relation(alloc, version)
                                        .indent(4),
                                ),
                            ),
                            alloc.text(name::LABELS_REL).append(" = ").append(
                                alloc
                                    .hardline()
                                    .append(self.make_labels_relation(alloc))
                                    .nest(4)
                                    .append(alloc.hardline())
                                    .parens(),
                            ),
                            alloc.text(name::ARG_CALL_SITE).append(" = ").append(
                                alloc
                                    .hardline()
                                    .append(
                                        self.make_callsite_argument_relation(alloc)
                                            .indent(4)
                                            .append(alloc.hardline()),
                                    )
                                    .parens(),
                            ),
                            alloc.text(name::FUN_REL).append(" = ").append(
                                //alloc.text(name::RETURN_CALL_SITE).append(" = ").append(
                                alloc
                                    .hardline()
                                    .append(
                                        self.make_return_func_relation(alloc)
                                            .indent(4)
                                            .append(alloc.hardline()),
                                    )
                                    .parens(),
                            ),
                            alloc.text(name::OTYPE_REL).append(" = ").append(
                                alloc
                                    .hardline()
                                    .append(
                                        self.make_otype_relation(alloc)
                                            .indent(4)
                                            .append(alloc.hardline()),
                                    )
                                    .parens(),
                                ),
                            alloc.text(name::FORMAL_PARAMETER_FUNCTION).append(" = ").append(
                                alloc.hardline()
                                .append(
                                    self.make_formal_param_relation(alloc).indent(4).append(alloc.hardline())
                                ).parens()
                            ),
                            if version == Version::V1 {
                                alloc.text(name::FORMAL_PARAMETER_ANNOTATION).append(" = ").append(
                                    alloc.hardline()
                                    .append(
                                        alloc.forge_relation_with_arity(3,
                                            self.annotations.iter()
                                                .flat_map(|(ident, (anns, _))|
                                                    anns.iter().filter_map(Annotation::as_label_ann)
                                                        .flat_map(|label|
                                                            label.refinement.on_argument().into_iter_set_in_domain().map(|i|
                                                                (
                                                                    std::iter::once(FormalParameter { position: i as u16, function: *ident }.build_forge(alloc)),
                                                                    std::iter::once(ident.build_forge(alloc).append("->").append(label.marker.as_str())))))
                                                )
                                        )
                                        .indent(4)
                                        .append(alloc.hardline())
                                    )
                                    .parens()
                                )
                            } else {
                                alloc.text(name::CTRL_CALLS).append(" = ").append(
                                    alloc.hardline().append(
                                        alloc.forge_relation_with_arity(2,
                                            self.controllers.iter().map(|(ctrl, data)| {
                                                let call_sites = data.ctrl_flow.0.iter().flat_map(|(from, to)|
                                                    from.as_function_call().into_iter().chain(to)
                                                ).chain(
                                                    data.data_flow.0.iter().flat_map(|(from, to)|
                                                    from.as_function_call().into_iter().chain(
                                                        to.iter().filter_map(|s| s.as_argument()).map(|a| a.0)
                                                    )
                                                )
                                                ).collect::<HashSet<_>>();

                                                (std::iter::once(ctrl.build_forge(alloc)),
                                                call_sites.into_iter().map(|cs| cs.build_forge(alloc))
                                                )
                                            })
                                        )
                                        .indent(4)
                                        .append(alloc.hardline())
                                    )
                                )
                            }
                        ])
                        .nest(4)
                        .append(alloc.hardline())
                        .braces(),
                ),
        ])
    }
}
