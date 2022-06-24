extern crate pretty;

use crate::HashSet;
use pretty::{DocAllocator, DocBuilder, Pretty};

use crate::desc::{DataSink, DataSource, Identifier, ProgramDescription, Relation, Sinks};

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

pub trait ToForge {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone;
}

impl ToForge for Identifier {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        alloc.text(self.as_str())
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
        alloc.intersperse(
            self.0.iter().map(|(src, sinks)| {
                src.as_forge(alloc).append("->").append(
                    alloc
                        .intersperse(
                            sinks.iter().map(|sink| sink.as_forge(alloc)),
                            alloc.text(" + "),
                        )
                        .parens(),
                )
            }),
            alloc.text(" +").append(alloc.hardline()),
        )
    }
}

fn data_sink_as_forge<'b, A: DocAllocator<'b, ()>>(
    alloc: &'b A,
    function: &'b Identifier,
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

impl ToForge for DataSource {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        match self {
            DataSource::FunctionCall(f) => alloc.text("call_").append(alloc.as_string(f)),
            DataSource::Argument(a) => alloc.text("arg").append(alloc.as_string(a)),
        }
    }
}

const SRC_NAME: &'static str = "Src";
const ARG_NAME: &'static str = "Arg";
const FN_CALL_NAME: &'static str = "Call";
const FN_NAME: &'static str = "Fn";
const CTRL_NAME: &'static str = "Ctrl";
const FLOW_NAME: &'static str = "flow";
const SENSITIVE_NAME: &'static str = "sensitive";
const WITNESS_NAME: &'static str = "witness";
const FLOWS_PREDICATE_NAME: &'static str = "Flows";

impl ToForge for ProgramDescription {
    fn as_forge<'b, 'a: 'b, A: DocAllocator<'b, ()>>(
        &'a self,
        alloc: &'b A,
    ) -> DocBuilder<'b, A, ()>
    where
        A::Doc: Clone,
    {
        /// For now the order here *must* be topological as the code gen does not reorder this automatically
        const SIGS: &[(
            &'static str,
            Option<&'static str>,
            &'static [(&'static str, &'static str)],
        )] = &[
            (SRC_NAME, None, &[]),
            (FN_NAME, None, &[]),
            (ARG_NAME, Some(SRC_NAME), &[]),
            (FN_CALL_NAME, Some(SRC_NAME), &[]),
            (
                CTRL_NAME,
                None,
                &[
                    (FLOW_NAME, "set Src->Fn"), // I'd have liked to define these types in terms of other string constants, but it seems rust doesn't let you concatenate strings at compile time
                    (SENSITIVE_NAME, "set Src"),
                    (WITNESS_NAME, "set Src"),
                ],
            ),
        ];

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
            alloc.lines(SIGS.iter().map(|(name, parent, fields)| {
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
                                            alloc.text(*name).append(": ").append(alloc.text(*typ))
                                        }),
                                        alloc.text(",").append(alloc.hardline()),
                                    )
                                    .indent(4)
                                    .append(alloc.hardline()),
                            )
                        }
                        .braces(),
                    )
            })),
            alloc.nil(),
            alloc.lines(self.all_sources().into_iter().map(|a| {
                make_one_sig(
                    alloc,
                    a.as_forge(alloc),
                    match a {
                        DataSource::Argument(_) => ARG_NAME,
                        DataSource::FunctionCall(_) => FN_CALL_NAME,
                    },
                )
            })),
            alloc.nil(),
            alloc.lines(self.annotations.iter().flat_map(|(name, sink)| {
                (0..sink.num_args).map(|arg_slot| {
                    make_one_sig(alloc, data_sink_as_forge(alloc, name, arg_slot), FN_NAME)
                })
            })),
            alloc.nil(),
            alloc.lines(
                self.controllers
                    .keys()
                    .map(|e| make_one_sig(alloc, e.as_forge(alloc), CTRL_NAME)),
            ),
            alloc.nil(),
            alloc
                .text("pred ")
                .append(FLOWS_PREDICATE_NAME)
                .append(" ")
                .append(
                    alloc
                        .hardline()
                        .append(
                            alloc
                                .lines(self.controllers.iter().map(|(e, ctrl)| {
                                    alloc.lines([
                                        e.as_forge(alloc)
                                            .append(".")
                                            .append(FLOW_NAME)
                                            .append(" = ")
                                            .append(
                                                alloc
                                                    .hardline()
                                                    .append(ctrl.flow.as_forge(alloc).indent(4))
                                                    .parens(),
                                            ),
                                        e.as_forge(alloc)
                                            .append(".")
                                            .append(WITNESS_NAME)
                                            .append(" = ")
                                            .append(ctrl.witnesses.as_forge(alloc)),
                                        e.as_forge(alloc)
                                            .append(".")
                                            .append(SENSITIVE_NAME)
                                            .append(" = ")
                                            .append(ctrl.sensitive.as_forge(alloc)),
                                    ])
                                }))
                                .indent(4)
                                .append(alloc.hardline()),
                        )
                        .braces(),
                ),
        ])
    }
}

pub(crate) fn generate_safety_constraints<'b, 'a: 'b, A: pretty::DocAllocator<'b, ()>>(
    alloc: &'a A,
    anns: &'a Sinks,
) -> DocBuilder<'b, A, ()>
where
    A::Doc: Clone,
{
    fn safety_predicate_name<'b, 'a: 'b, A: pretty::DocAllocator<'b, ()>>(
        alloc: &'a A,
        name: &Identifier,
    ) -> DocBuilder<'b, A, ()> {
        alloc.as_string(name).append("IsSafe")
    }

    alloc.lines(
        anns.iter()
            .map(|(id, marked)| {
                alloc
                    .text("pred ")
                    .append(
                        safety_predicate_name(alloc, id)
                            .append(alloc.text("ctrl: one ").append(CTRL_NAME).brackets()),
                    )
                    .append(
                        alloc
                            .hardline()
                            .append(
                                alloc
                                    .text("all s: ctrl.")
                                    .append(SENSITIVE_NAME)
                                    .append(" & ")
                                    .append(SRC_NAME)
                                    .append(" |")
                                    .append(alloc.hardline())
                                    .append(
                                        alloc
                                            .lines([
                                                alloc.text("some ").append(
                                                    alloc
                                                        .text("s->")
                                                        .append(
                                                            alloc
                                                                .intersperse(
                                                                    marked.ann.leaks.iter().map(
                                                                        |l| {
                                                                            alloc
                                                                                .as_string(id)
                                                                                .append("_")
                                                                                .append(
                                                                                    alloc
                                                                                        .as_string(
                                                                                            l,
                                                                                        ),
                                                                                )
                                                                        },
                                                                    ),
                                                                    " + ",
                                                                )
                                                                .parens(),
                                                        )
                                                        .parens()
                                                        .append(" & ctrl.")
                                                        .append(FLOW_NAME),
                                                ),
                                                alloc
                                                    .text("implies ctrl.")
                                                    .append(WITNESS_NAME)
                                                    .append("->")
                                                    .append(
                                                        alloc
                                                            .intersperse(
                                                                marked.ann.scopes.iter().map(|s| {
                                                                    alloc
                                                                        .as_string(id)
                                                                        .append("_")
                                                                        .append(alloc.as_string(s))
                                                                }),
                                                                " + ",
                                                            )
                                                            .parens(),
                                                    )
                                                    .append(" in ctrl.")
                                                    .append(FLOW_NAME),
                                            ])
                                            .indent(4),
                                    )
                                    .indent(4),
                            )
                            .append(alloc.hardline())
                            .braces(),
                    )
            })
            .chain([alloc.text("test expect ").append(
                alloc
                    .hardline()
                    .append(
                        alloc
                            .text("safety_properties: ")
                            .append(
                                alloc
                                    .hardline()
                                    .append(
                                        alloc
                                            .text(FLOWS_PREDICATE_NAME)
                                            .append(" implies ")
                                            .append(
                                                alloc
                                                    .text("all c: ")
                                                    .append(CTRL_NAME)
                                                    .append(" |")
                                                    .append(
                                                        alloc
                                                            .hardline()
                                                            .append(
                                                                alloc
                                                                    .lines(anns.keys().map(|i| {
                                                                        safety_predicate_name(
                                                                            alloc, i,
                                                                        )
                                                                        .append(
                                                                            alloc
                                                                                .text("c")
                                                                                .brackets(),
                                                                        )
                                                                    }))
                                                                    .indent(4),
                                                            )
                                                            .append(alloc.hardline())
                                                            .braces(),
                                                    )
                                                    .parens(),
                                            )
                                            .indent(4),
                                    )
                                    .append(alloc.hardline())
                                    .braces()
                                    .append(" is theorem"),
                            )
                            .indent(4),
                    )
                    .append(alloc.hardline())
                    .braces(),
            )]),
    )
}
