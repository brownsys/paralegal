extern crate pretty;

use crate::{desc::CallSite, HashSet};
use pretty::{DocAllocator, DocBuilder, Pretty};

use std::borrow::Cow;

use crate::desc::{
    Annotation, Ctrl, DataSink, DataSource, Identifier, ObjectType, ProgramDescription, Relation,
};

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

trait DocFrgRel<'a, A = ()>: DocAllocator<'a, A>
where
    A: 'a,
{
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
            self.text("none->none")
        }
    }
}

impl<'a, T, A> DocFrgRel<'a, A> for T
where
    T: DocAllocator<'a, A>,
    A: 'a,
{
}

pub trait ToForge {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone;
}

lazy_static! {
    static ref FORGE_RESERVED_SYMBOLS: HashSet<Identifier> = [
        "expect", "test", "implies", "is", "not", "some", "all", "sig", "pred", "no", "one", "sig",
        "open", "and", "abstract", "extends", "none", "set"
    ]
    .into_iter()
    .map(Identifier::from_str)
    .collect();
}

impl ToForge for Identifier {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.text(if FORGE_RESERVED_SYMBOLS.contains(self) {
            Cow::Owned("s__".to_string() + self.as_str())
        } else {
            Cow::Borrowed(self.as_str())
        })
    }
}

impl<X: ToForge, Y: ToForge> ToForge for Relation<X, Y> {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.forge_relation(self.0.iter().map(|(src, sinks)| {
            (
                std::iter::once(src.as_forge(alloc)),
                sinks.iter().map(|sink| sink.as_forge(alloc)),
            )
        }))
    }
}

fn data_sink_as_forge<'b, A: DocAllocator<'b, ()>>(
    alloc: &'b A,
    function: &'b CallSite,
    arg_slot: usize,
) -> DocBuilder<'b, A, ()>
where
    A::Doc: Clone,
{
    function
        .as_forge(alloc)
        .append(alloc.text("_"))
        .append(alloc.as_string(arg_slot))
}

impl ToForge for DataSink {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        data_sink_as_forge(alloc, &self.function, self.arg_slot)
    }
}

impl<T: ToForge> ToForge for HashSet<T> {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        if self.is_empty() {
            alloc.text("none")
        } else {
            alloc.intersperse(self.iter().map(|w| w.as_forge(alloc)), "+")
        }
    }
}

impl ToForge for CallSite {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.text(format!(
            "b{}_i{}",
            self.location.block.as_usize(),
            self.location.statement_index
        ))
    }
}

fn data_source_as_forge<'b, A: DocAllocator<'b, ()>>(
    src: &'b DataSource,
    alloc: &'b A,
) -> DocBuilder<'b, A, ()>
where
    A::Doc: Clone,
{
    match src {
        DataSource::FunctionCall(f) => alloc.text("call_").append(f.as_forge(alloc)),
        DataSource::Argument(a) => alloc.text("arg_").append(alloc.as_string(a)),
    }
}

impl ToForge for DataSource {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        data_source_as_forge(self, alloc)
    }
}

mod name {
    pub const SRC: &'static str = "Src";
    /// Previously "Arg"
    pub const INPUT_ARGUMENT: &'static str = "InputArgument";
    /// Previously "Call"
    pub const CALL_ARGUMENT_OUTPUT: &'static str = "FnOut";
    /// Previously "Fn"
    pub const CALL_SITE: &'static str = "CallSite";
    /// Previously "CallSite"
    pub const CALL_ARGUMENT: &'static str = "CallArgument";
    pub const FUNCTION: &'static str = "Function";
    pub const FUN_REL: &'static str = "function";
    pub const CTRL: &'static str = "Ctrl";
    pub const FLOW: &'static str = "flow";
    pub const FLOWS_PREDICATE: &'static str = "Flows";
    pub const OBJ: &'static str = "Object";
    pub const LABEL: &'static str = "Label";
    pub const LABELS_REL: &'static str = "labels";
    pub const TYPES: &'static str = "types";
    pub const TYPE: &'static str = "Type";
    pub const ARG_CALL_SITE: &'static str = "arg_call_site";
    pub const RETURN_CALL_SITE: &'static str = "ret_call_site";
    pub const OTYPE_REL: &'static str = "otype";
    pub const EXCEPTIONS_LABEL: &'static str = "exception";

    lazy_static! {
        /// For now the order here *must* be topological as the code gen does not reorder this automatically
        pub static ref SIGS: Vec<(
                &'static str,
                Option<&'static str>,
                Vec<(&'static str, String)>,
            )> = {
                let set = |i| "set ".to_string() + i;
                let one = |i| "one ".to_string() + i;
                let arr = |from: &str, to| from.to_string() + "->" + to;
                vec![
                    (LABEL, None, vec![]),
                    (OBJ, None, vec![(LABELS_REL, set(LABEL))]),
                    (FUNCTION, Some(OBJ), vec![]),
                    (SRC, Some(OBJ), vec![]),
                    (CALL_SITE, Some(OBJ), vec![(FUN_REL, one(FUNCTION))]),
                    (CALL_ARGUMENT, Some(OBJ), vec![(ARG_CALL_SITE, one(CALL_SITE))]),
                    (INPUT_ARGUMENT, Some(SRC), vec![]),
                    (TYPE, Some(OBJ), vec![(OTYPE_REL, set(TYPE))]),
                    (CALL_ARGUMENT_OUTPUT, Some(SRC), vec![(RETURN_CALL_SITE, one(CALL_SITE))]),
                    (
                        CTRL,
                        None,
                        vec![
                            (FLOW, set(&arr(SRC, CALL_ARGUMENT))),
                            (TYPES, set(&arr(SRC, TYPE))),
                        ],
                    ),
                ]
            };
    }
}

fn make_one_sig<'b, A: DocAllocator<'b, ()>, I: Pretty<'b, A, ()>>(
    alloc: &'b A,
    inner: I,
    parent: &'static str,
) -> DocBuilder<'b, A, ()>
where
    A::Doc: Clone,
{
    alloc
        .text("one sig ")
        .append(inner)
        .append(" extends ")
        .append(parent)
        .append(" {}")
}

fn make_forge_sigs<'a, A: DocAllocator<'a, ()>>(alloc: &'a A) -> DocBuilder<'a, A, ()>
where
    A::Doc: Clone,
{
    alloc.lines(name::SIGS.iter().map(|(name, parent, fields)| {
        alloc
            .text("abstract sig ")
            .append(*name)
            .append(parent.map_or(alloc.nil(), |p| alloc.text(" extends ").append(p)))
            .append(alloc.space())
            .append(
                if fields.is_empty() {
                    alloc.nil()
                } else {
                    alloc.hardline().append(
                        alloc
                            .intersperse(
                                fields.iter().map(|(name, typ)| {
                                    alloc.text(*name).append(": ").append(alloc.text(typ))
                                }),
                                alloc.text(",").append(alloc.hardline()),
                            )
                            .indent(4)
                            .append(alloc.hardline()),
                    )
                }
                .braces(),
            )
    }))
}

impl ProgramDescription {
    fn make_label_sigs<'a, A: DocAllocator<'a, ()>>(&self, alloc: &'a A) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.lines(
            self.annotations
                .values()
                .flat_map(|v| v.0.iter())
                .filter_map(Annotation::as_label_ann)
                .map(|a| a.label)
                .chain(std::iter::once(crate::Symbol::intern(
                    name::EXCEPTIONS_LABEL,
                )))
                .collect::<HashSet<_>>()
                .into_iter()
                .map(|s| make_one_sig(alloc, alloc.text(s.as_str().to_string()), name::LABEL)),
        )
    }

    fn make_source_sigs<'a, 'b: 'a, A: DocAllocator<'a, ()>>(
        &'b self,
        alloc: &'a A,
    ) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.lines(
            self.all_sources()
                .chain(self.controllers.values().flat_map(|c| c.types.keys()))
                .collect::<HashSet<_>>()
                .iter()
                .map(|a| {
                    make_one_sig(
                        alloc,
                        a.as_forge(alloc),
                        match a {
                            DataSource::Argument(_) => name::INPUT_ARGUMENT,
                            DataSource::FunctionCall(_) => name::CALL_ARGUMENT_OUTPUT,
                        },
                    )
                }),
        )
    }

    fn make_sink_sigs<'a, 'b: 'a, A: DocAllocator<'a, ()>>(
        &'b self,
        alloc: &'a A,
    ) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.lines(self.all_sinks().into_iter().map(|sink| {
            make_one_sig(
                alloc,
                data_sink_as_forge(alloc, &sink.function, sink.arg_slot),
                name::CALL_ARGUMENT,
            )
        }))
    }

    fn make_type_sigs<'a, 'b: 'a, A: DocAllocator<'a, ()>>(
        &'b self,
        alloc: &'a A,
    ) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.lines(
            self.annotations
                .iter()
                .filter(|t| t.1 .1 == ObjectType::Type)
                .map(|(name, _)| make_one_sig(alloc, name.as_forge(alloc), name::TYPE)),
        )
    }

    fn make_function_sigs<'a, 'b: 'a, A: DocAllocator<'a, ()>>(
        &'b self,
        alloc: &'a A,
    ) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.lines(
            self.all_functions()
                .into_iter()
                .map(|f| make_one_sig(alloc, f.as_forge(alloc), name::FUNCTION)),
        )
    }

    fn make_labels_relation<'a, 'b: 'a, A: DocAllocator<'a, ()>>(
        &'b self,
        alloc: &'a A,
    ) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc
            .forge_relation(self.annotations.iter().flat_map(|(id, (anns, _))| {
                // I've decided to do the more
                // complicated thing here which
                // restores the old behavior. Is
                // this the right thing to do?
                // Maybe, maybe not. Only time will
                // tell.
                //
                // The "old behavior" I am restoring is that
                anns.iter()
                    .filter_map(Annotation::as_label_ann)
                    .map(move |a| {
                        (
                            if a.refinement.on_return() {
                                Some(self.all_sources().filter(|s| {
                                    s.as_function_call().map_or(false, |c| &c.function == id)
                                }))
                            } else {
                                None
                            }
                            .into_iter()
                            .flat_map(|i| i)
                            .map(|ds| ds.as_forge(alloc))
                            .chain(
                                self.all_sinks()
                                    .into_iter()
                                    .filter(|s| {
                                        &s.function.function == id
                                            && a.refinement
                                                .on_argument()
                                                .contains(&(s.arg_slot as u16))
                                    })
                                    .map(|s| s.as_forge(alloc)),
                            )
                            // This is necessary because otherwise captured variables escape
                            .collect::<Vec<_>>()
                            .into_iter(),
                            std::iter::once(alloc.text(a.label.as_str())),
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
                            .map(|_| id.as_forge(alloc))
                            .into_iter(),
                        std::iter::once(alloc.text(name::EXCEPTIONS_LABEL)),
                    )
                })),
            )
    }

    fn make_callsite_argument_relation<'a, 'b: 'a, A: DocAllocator<'a, ()>>(
        &'b self,
        alloc: &'a A,
    ) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.forge_relation(self.all_sinks().into_iter().map(|src| {
            (
                std::iter::once(src.as_forge(alloc)),
                std::iter::once(src.function.as_forge(alloc)),
            )
        }))
    }

    fn make_return_func_relation<'a, 'b: 'a, A: DocAllocator<'a, ()>>(
        &'b self,
        alloc: &'a A,
    ) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.forge_relation(self.all_sources().into_iter().filter_map(|src| match src {
            DataSource::FunctionCall(f) => Some((
                std::iter::once(src.as_forge(alloc)),
                std::iter::once(f.as_forge(alloc)),
            )),
            _ => None,
        }))
    }

    fn make_otype_relation<'a, 'b: 'a, A: DocAllocator<'a, ()>>(
        &'b self,
        alloc: &'a A,
    ) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.forge_relation(self.annotations.iter().map(|(o, (anns, _))| {
            (
                std::iter::once(o.as_forge(alloc)),
                anns.iter()
                    .filter_map(Annotation::as_otype_ann)
                    .flat_map(|v| v.iter())
                    .map(|t| t.as_forge(alloc)),
            )
        }))
    }
}

impl Ctrl {
    fn make_types_relation<'a, 'b: 'a, A: DocAllocator<'a, ()>>(
        &'b self,
        alloc: &'a A,
    ) -> DocBuilder<'a, A, ()>
    where
        A::Doc: Clone,
    {
        alloc
            .hardline()
            .append(alloc.forge_relation(self.types.iter().map(|(i, desc)| {
                (
                    std::iter::once(data_source_as_forge(i, alloc)),
                    desc.iter().map(|t| alloc.text(t.as_str())),
                )
            })))
    }
}

impl ToForge for ProgramDescription {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.lines([
            alloc.text("#lang forge"),
            alloc.nil(),
            alloc
                .text("/* This file is auto-generated by ")
                .append(crate_name!())
                .append(" version ")
                .append(crate_version!())
                .append(". */"),
            alloc.nil(),
            make_forge_sigs(alloc),
            alloc.nil(),
            self.make_label_sigs(alloc),
            alloc.nil(),
            self.make_source_sigs(alloc),
            alloc.nil(),
            self.make_sink_sigs(alloc),
            self.make_type_sigs(alloc),
            self.make_function_sigs(alloc),
            alloc.nil(),
            alloc.lines(
                self.controllers
                    .keys()
                    .map(|e| make_one_sig(alloc, e.as_forge(alloc), name::CTRL)),
            ),
            alloc.nil(),
            alloc
                .text("pred ")
                .append(name::FLOWS_PREDICATE)
                .append(" ")
                .append(
                    alloc
                        .lines([
                            alloc.nil(),
                            alloc.lines(self.controllers.iter().map(|(e, ctrl)| {
                                alloc.lines([
                                    e.as_forge(alloc)
                                        .append(".")
                                        .append(name::FLOW)
                                        .append(" = ")
                                        .append(
                                            alloc
                                                .hardline()
                                                .append(ctrl.flow.as_forge(alloc).indent(4))
                                                .append(alloc.hardline())
                                                .parens(),
                                        ),
                                    e.as_forge(alloc)
                                        .append(".")
                                        .append(name::TYPES)
                                        .append(" = ")
                                        .append(
                                            ctrl.make_types_relation(alloc)
                                                .nest(4)
                                                .append(alloc.hardline())
                                                .parens(),
                                        ),
                                ])
                            })),
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
                            alloc.text(name::RETURN_CALL_SITE).append(" = ").append(
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
                        ])
                        .nest(4)
                        .append(alloc.hardline())
                        .braces(),
                ),
        ])
    }
}
