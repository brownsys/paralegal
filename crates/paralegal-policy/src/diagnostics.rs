//! Emit messages to the user running a policy.
//!
//! The diagnostics of a Paralegal policy are similar to those used in rustc. In
//! particular we use a strategy of "keep going", meaning that a policy should
//! not fail at the first error. Instead it should attempt to keep going if
//! possible and emit additional errors, as those messages are useful for the
//! user.
//!
//! This manifests for instance in [`Diagnostics::error`]. This function records
//! a severe error that should fail the policy but it does not exit the program.
//! Instead the message is recorded and emitted later, for instance by
//! [`Context::emit_diagnostics`].
//!
//! ## Emitting Messages
//!
//! The main interface for diagnostics is the [`Diagnostics`] trait which
//! defines functions for emitting messages like [`error`][Diagnostics::error]
//! for policy failures and [`warning`][Diagnostics::warning] for indicators to
//! the user that something may be off, but not causing a policy failure.
//!
//! We also offer two convenience macros [`assert_error!`](crate::assert_error) and
//! [`assert_warning!`](crate::assert_warning) that correspond to either function. Much like
//! [`assert!`] they only evaluate and emit their messages if the provided
//! condition is `false`. They should be used like `assert_warning!(ctx,
//! condition, message)`. `ctx` here is anything that implements
//! [`Diagnostics`].
//!
//! [`Diagnostics`] is implemented directly by [`Context`] so you can use
//! `ctx.error()` or `ctx.warning()`. You can also call it on scoped contexts
//! (see below).
//!
//! ## Scoping messages
//!
//! You may however add additional contextual information about which policy or
//! combinator is currently executing. [`Context::named_policy`] returns a
//! wrapper that can be used the same way that you use [`Context`], but when
//! [`error`][Diagnostics::error] or [`warning`][Diagnostics::warning] is called
//! it also appends the name of the policy to you specified.
//!
//! Similarly you can use [`Context::named_combinator`] or
//! [`PolicyContext::named_combinator`] to add context about a named combinator.
//!
//! ## Intended Workflow
//!
//! ```no_run
//! use paralegal_policy::{
//!     Context, RootContext, assert_error, assert_warning,
//!     paralegal_spdg::Identifier
//! };
//! use std::sync::Arc;
//!
//! fn my_check(ctx: Arc<RootContext>) {
//!     ctx.named_policy(Identifier::new_intern("cannot escape"), |ctx| {
//!         let result_1 = ctx.clone().named_combinator(
//!             Identifier::new_intern("collect something"),
//!             |ctx| {
//!                 /* actual computation */
//!                 assert_error!(ctx, 1 + 2 == 4, "Oh oh, fail!");
//!                 true
//!             }
//!         );
//!         let result_2 = ctx.clone().named_combinator(
//!             Identifier::new_intern("reach something"),
//!             |ctx| {
//!                 assert_warning!(ctx, 1 - 3 == 0, "maybe wrong?");
//!                 false
//!             }
//!         );
//!         assert_error!(ctx, result_1 || result_2, "combination failure");
//!     })
//!
//! }
//! ```
//!
//! The messages emitted from here (if all conditions fail true) would be
//!
//! ```text
//! [policy: cannot escape] [collect something] Oh oh, fail!
//! [policy: cannot escape] [reach something] maybe wrong?
//! [policy: cannot escape] combination failure
//! ```
//!
//! It is recommended to use this "shadowing" approach, where all contexts are
//! named `ctx`, to avoid using the outer context by accident. The methods off
//! outer contexts are always available on the inner ones.
//!
//! Note that some methods, like [`Context::always_happens_before`] add a named
//! combinator context by themselves when you use their
//! [`report`][crate::algo::ahb::AlwaysHappensBefore::report] functions.

#![allow(clippy::arc_with_non_send_sync)]

use colored::*;
use indexmap::IndexMap;

use std::rc::Rc;
use std::{io::Write, sync::Arc};

use paralegal_spdg::{DisplayPath, Endpoint, GlobalNode, Identifier, Span, SpanCoord, SPDG};

use crate::{Context, NodeExt, RootContext};

/// Check the condition and emit a [`Diagnostics::error`] if it fails.
#[macro_export]
macro_rules! assert_error {
    ($ctx:expr, $cond: expr $(,)?) => {
        assert_error!($ctx, $cond, "Error: {}", stringify!($cond))
    };
    ($ctx:expr, $cond: expr, $msg:expr $(,)?) => {
        if !$cond {
            use $crate::diagnostics::Diagnostics;
            Diagnostics::error(&$ctx, $msg);
        }
    };
    ($ctx:expr, $cond: expr, $msg:expr, $($frag:expr),+ $(,)?) => {
        if !$cond {
            use $crate::diagnostics::Diagnostics;
            Diagnostics::error(&$ctx, format!($msg, $($frag),+));
        }
    };
}

/// Check the condition and emit a [`Diagnostics::warning`] if it fails.
#[macro_export]
macro_rules! assert_warning {
    ($ctx:expr, $cond: expr $(,)?) => {
        assert_warning!($ctx, $cond, "Warning: {}", stringify!($cond))
    };
    ($ctx:expr, $cond: expr, $msg:expr $(,)?) => {
        if !$cond {
            use $crate::diagnostics::Diagnostics;
            Diagnostics::warning(&$ctx, $msg);
        }
    };
    ($ctx:expr, $cond: expr, $msg:expr, $($frag:expr),+ $(,)?) => {
        if !$cond {
            use $crate::diagnostics::Diagnostics;
            Diagnostics::warning(&$ctx, format!($msg, $($frag),+));
        }
    };
}

/// Severity of a recorded diagnostic message
#[derive(Debug, Clone, Copy, strum::AsRefStr, Hash, PartialEq, Eq)]
#[strum(serialize_all = "snake_case")]
pub enum Severity {
    /// This indicates that the policy failed.
    Error,
    /// This could indicate that the policy does not operate as intended.
    Warning,
    /// Additional information for a diagnostic
    Note,
    /// Some helpful hint
    Help,
}

impl Severity {
    fn must_abort(self) -> bool {
        matches!(self, Severity::Error)
    }

    fn color(self) -> Color {
        match self {
            Severity::Error => Color::Red,
            Severity::Warning => Color::Yellow,
            Severity::Note => Color::Blue,
            Severity::Help => Color::Green,
        }
    }
}

/// Context provided to [`HasDiagnosticsBase::record`].
type DiagnosticContextStack = Vec<Identifier>;

#[derive(Hash, PartialEq, Eq)]
/// Representation of a diagnostic message. You should not interact with this
/// type directly but use the methods on [`Diagnostics`] or
/// [`DiagnosticBuilder`] to create these.
#[derive(Debug)]
pub struct Diagnostic {
    context: DiagnosticContextStack,
    children: Vec<DiagnosticPart>,
}

impl Diagnostic {
    fn write(&self, w: &mut impl std::fmt::Write) -> std::fmt::Result {
        for ctx in self.context.iter().rev() {
            write!(w, "{ctx} ")?;
        }
        for c in &self.children {
            c.write(w)?;
        }
        Ok(())
    }
}

#[derive(Hash, PartialEq, Eq, Debug)]
struct DiagnosticPart {
    message: String,
    severity: Severity,
    span: Option<Box<HighlightedSpan>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SubSpan {
    start: SpanCoord,
    end: SpanCoord,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
/// A span with only a portion highlighted.
pub struct HighlightedSpan {
    span: Span,
    highlight: Option<SubSpan>,
}

impl HighlightedSpan {
    /// Create a  new span with a highlighted section
    pub fn new(span: Span, start: SpanCoord, end: SpanCoord) -> Self {
        assert!(start >= span.start);
        assert!(end <= span.end);
        assert!(start <= end);
        HighlightedSpan {
            span,
            highlight: Some(SubSpan { start, end }),
        }
    }
}

impl From<Span> for HighlightedSpan {
    fn from(value: Span) -> Self {
        Self {
            span: value,
            highlight: None,
        }
    }
}

impl DiagnosticPart {
    fn write(&self, s: &mut impl std::fmt::Write) -> std::fmt::Result {
        let severity = self.severity;
        let coloring = severity.color();

        use std::io::BufRead;

        writeln!(s, "{}: {}", severity.as_ref().color(coloring), self.message)?;
        if let Some(src_loc) = &self.span {
            let start_line = src_loc.span.start.line as usize;
            let start_col = src_loc.span.start.col as usize;
            let end_line = src_loc.span.end.line as usize;
            let end_col = src_loc.span.end.col as usize;
            let (hl_start_line, hl_start_col, hl_end_line, hl_end_col) =
                if let Some(hl) = &src_loc.highlight {
                    (
                        hl.start.line as usize,
                        hl.start.col as usize,
                        hl.end.line as usize,
                        hl.end.col as usize,
                    )
                } else {
                    (start_line, start_col, end_line, end_col)
                };
            let max_line_len =
                std::cmp::max(start_line.to_string().len(), end_line.to_string().len());
            let tab: String = " ".repeat(max_line_len);
            writeln!(
                s,
                "{tab}{} {}:{}:{}",
                "-->".blue(),
                src_loc.span.source_file.file_path,
                start_line,
                start_col,
            )?;
            writeln!(s, "{tab} {}", "|".blue())?;
            let path = &src_loc.span.source_file.abs_file_path;
            let file = match std::fs::File::open(path) {
                Ok(file) => file,
                Err(e) => {
                    writeln!(s, "Error: {e:?} in file {}", path.display())?;
                    return Ok(());
                }
            };

            let lines = std::io::BufReader::new(file)
                .lines()
                .skip(start_line - 1)
                .take(end_line - start_line + 1)
                .enumerate();
            for (i, line) in lines {
                let line_content: String = line.unwrap();
                let line_num = start_line + i;

                writeln!(
                    s,
                    "{:<max_line_len$} {} {}",
                    &line_num.to_string().blue(),
                    "|".blue(),
                    line_content.replace('\t', &" ".repeat(TAB_SIZE))
                )?;
                if line_num >= hl_start_line && line_num <= hl_end_line {
                    let end: usize = if line_num == hl_end_line {
                        line_length_while(&line_content[0..hl_end_col - 1], |_| true)
                    } else {
                        line_length_while(&line_content, |_| true)
                    };
                    let start: usize = if line_num == hl_start_line {
                        line_length_while(&line_content[0..hl_start_col - 1], |_| true)
                    } else {
                        line_length_while(&line_content, char::is_whitespace)
                    };
                    let highlight_len = if end < start {
                        // TODO figure out how this happens
                        0
                    } else {
                        end - start
                    };
                    write!(s, "{tab} {} {:start$}", "|".blue(), "")?;
                    for _ in 0..highlight_len {
                        write!(s, "{}", "^".color(coloring))?;
                    }
                    writeln!(s)?;
                }
            }
            writeln!(s, "{tab} {}", "|".blue())?;
        }

        Ok(())
    }
}

/// Facility to create structured diagnostics including spans and multi-part
/// messages. New builders are created with methods on [`Diagnostics`].
/// `struct_<severity>` creates simple main diagnostics with only a message,
/// `struct_node_<severity>` creates a main diagnostic with a message and the
/// span of a graph node and `struct_span_<severity>` creates a main diagnostic
/// with a message and a custom source code span.
///
/// The builder allows chaining additional sub diagnostics to the main
/// diagnostic. Analogous to the initializers the `with_<severity>` family of
/// functions adds simple messages, `with_node_<severity>` adds messages with
/// spans from a node and `with_span_<severity>` adds messages with custom
/// spans.
///
/// Make sure to call [`Self::emit`] after construction, otherwise the
/// diagnostic is not shown.
#[derive(Debug)]
#[must_use = "you must call `emit`, otherwise the message is not shown"]
pub struct DiagnosticBuilder<'a, A: ?Sized> {
    diagnostic: Diagnostic,
    base: &'a A,
}

impl<'a, A: ?Sized> DiagnosticBuilder<'a, A> {
    fn init(
        message: String,
        severity: Severity,
        span: Option<impl Into<HighlightedSpan>>,
        base: &'a A,
    ) -> Self {
        DiagnosticBuilder {
            diagnostic: Diagnostic {
                context: vec![],
                children: vec![DiagnosticPart {
                    message,
                    severity,
                    span: span.map(Into::into).map(Box::new),
                }],
            },
            base,
        }
    }

    fn with_child(
        &mut self,
        message: impl Into<String>,
        severity: Severity,
        span: Option<impl Into<HighlightedSpan>>,
    ) -> &mut Self {
        self.diagnostic.children.push(DiagnosticPart {
            message: message.into(),
            severity,
            span: span.map(Into::into).map(Box::new),
        });
        self
    }
}

impl<'a, A: HasDiagnosticsBase + ?Sized> DiagnosticBuilder<'a, A> {
    /// Queue the diagnostic for display to the user.
    pub fn emit(self) {
        self.base.record(self.diagnostic)
    }

    /// Append a help message to the diagnostic.
    pub fn with_help(&mut self, message: impl Into<String>) -> &mut Self {
        self.with_child(message, Severity::Help, Option::<HighlightedSpan>::None)
    }

    /// Append a help message with a source code span to the diagnostic.
    pub fn with_span_help(&mut self, span: Span, message: impl Into<String>) -> &mut Self {
        self.with_child(message, Severity::Help, Some(span))
    }

    /// Append a help message and the span of a graph node to the diagnostic.
    pub fn with_node_help(&mut self, node: GlobalNode, message: impl Into<String>) -> &mut Self {
        self.with_node(Severity::Help, node, message.into())
    }

    /// Append a warning to the diagnostic.
    pub fn with_warning(&mut self, message: impl Into<String>) -> &mut Self {
        self.with_child(message, Severity::Warning, Option::<HighlightedSpan>::None)
    }

    /// Append a warning and the span of a graph node to the diagnostic.
    pub fn with_span_warning(&mut self, span: Span, message: impl Into<String>) -> &mut Self {
        self.with_child(message, Severity::Warning, Some(span))
    }

    /// Append a warning with a source code span to the diagnostic.
    pub fn with_node_warning(&mut self, node: GlobalNode, message: impl Into<String>) -> &mut Self {
        self.with_node(Severity::Warning, node, message.into())
    }

    /// Append a note to the diagnostic.
    pub fn with_note(&mut self, message: impl Into<String>) -> &mut Self {
        self.with_child(message, Severity::Note, Option::<HighlightedSpan>::None)
    }

    /// Append a note with a source code span to the diagnostic.
    pub fn with_span_note(&mut self, span: Span, message: impl Into<String>) -> &mut Self {
        self.with_child(message.into(), Severity::Note, Some(span))
    }

    /// Append a note and the span of a graph node to the diagnostic.
    pub fn with_node_note(&mut self, node: GlobalNode, message: impl Into<String>) -> &mut Self {
        self.with_node(Severity::Note, node, message.into())
    }

    fn with_node(&mut self, severity: Severity, node: GlobalNode, message: String) -> &mut Self {
        self.with_child(
            message,
            severity,
            Some(highlighted_node_span(self.base.as_ctx(), node)),
        )
    }
}

/// Low level machinery for diagnostics.
///
/// As a user you should only be using methods from [`Diagnostics`]. It
/// may however be helpful to look at the implementors of this trait, as those
/// are also implementors of [`Diagnostics`].
pub trait HasDiagnosticsBase {
    /// Base function for recording new diagnostics.
    ///
    /// This should be used by implementors of new wrappers, users should use
    /// high level functions like [`Diagnostics::error`] or
    /// [`Diagnostics::warning`] instead.
    fn record(&self, diagnostic: Diagnostic);

    /// Access to [`Context`], usually also available via [`std::ops::Deref`].
    fn as_ctx(&self) -> &RootContext;
}

impl<T: HasDiagnosticsBase> HasDiagnosticsBase for Arc<T> {
    fn record(&self, diagnostic: Diagnostic) {
        let t: &T = self.as_ref();
        t.record(diagnostic)
    }

    fn as_ctx(&self) -> &RootContext {
        self.as_ref().as_ctx()
    }
}

impl<T: HasDiagnosticsBase> HasDiagnosticsBase for &'_ T {
    fn as_ctx(&self) -> &RootContext {
        (*self).as_ctx()
    }

    fn record(&self, diagnostic: Diagnostic) {
        (*self).record(diagnostic)
    }
}

impl<T: HasDiagnosticsBase> HasDiagnosticsBase for Rc<T> {
    fn as_ctx(&self) -> &RootContext {
        (**self).as_ctx()
    }

    fn record(&self, diagnostic: Diagnostic) {
        (**self).record(diagnostic)
    }
}

/// User-facing methods to emit diagnostics.
///
/// This is how any types implementing [`HasDiagnosticsBase`] should actually be
/// used.
pub trait Diagnostics: HasDiagnosticsBase {
    /// Initialize a diagnostic builder for an error.
    ///
    /// This will fail the policy.
    fn struct_error(&self, msg: impl Into<String>) -> DiagnosticBuilder<'_, Self> {
        DiagnosticBuilder::init(
            msg.into(),
            Severity::Error,
            Option::<HighlightedSpan>::None,
            self,
        )
    }

    /// Initialize a diagnostic builder for an error with a source code span.
    ///
    /// This will fail the policy.
    fn struct_span_error(
        &self,
        span: impl Into<HighlightedSpan>,
        msg: impl Into<String>,
    ) -> DiagnosticBuilder<'_, Self> {
        DiagnosticBuilder::init(msg.into(), Severity::Error, Some(span), self)
    }

    /// Initialize a diagnostic builder for a warning.
    ///
    /// Does not fail the policy.
    fn struct_warning(&self, msg: impl Into<String>) -> DiagnosticBuilder<'_, Self> {
        DiagnosticBuilder::init(
            msg.into(),
            Severity::Warning,
            Option::<HighlightedSpan>::None,
            self,
        )
    }

    /// Initialize a diagnostic builder for a warning with a source code span
    ///
    /// Does not fail the policy.
    fn struct_span_warning(
        &self,
        span: impl Into<HighlightedSpan>,
        msg: impl Into<String>,
    ) -> DiagnosticBuilder<'_, Self> {
        DiagnosticBuilder::init(msg.into(), Severity::Warning, Some(span), self)
    }

    /// Initialize a diagnostic builder for a help message.
    fn struct_help(&self, msg: impl Into<String>) -> DiagnosticBuilder<'_, Self> {
        DiagnosticBuilder::init(
            msg.into(),
            Severity::Help,
            Option::<HighlightedSpan>::None,
            self,
        )
    }

    /// Initialize a diagnostic builder for a help message with a source code span
    fn struct_span_help(
        &self,
        span: impl Into<HighlightedSpan>,
        msg: impl Into<String>,
    ) -> DiagnosticBuilder<'_, Self> {
        DiagnosticBuilder::init(msg.into(), Severity::Help, Some(span), self)
    }

    /// Initialize a diagnostic builder for a note
    fn struct_note(&self, msg: impl Into<String>) -> DiagnosticBuilder<'_, Self> {
        DiagnosticBuilder::init(
            msg.into(),
            Severity::Note,
            Option::<HighlightedSpan>::None,
            self,
        )
    }

    /// Initialize a diagnostic builder for a note with a source code span
    fn struct_span_note(
        &self,
        span: impl Into<HighlightedSpan>,
        msg: impl Into<String>,
    ) -> DiagnosticBuilder<'_, Self> {
        DiagnosticBuilder::init(msg.into(), Severity::Note, Some(span), self)
    }

    /// Emit a message that is severe enough that it causes the policy to fail.
    fn error(&self, msg: impl Into<String>) {
        self.struct_error(msg).emit()
    }

    /// Emit a message that indicates to the user that the policy might be
    /// fraudulent but could be correct.
    fn warning(&self, msg: impl Into<String>) {
        self.struct_warning(msg).emit()
    }

    /// Emit a message that provides additional information to the user.
    fn note(&self, msg: impl Into<String>) {
        self.struct_note(msg).emit()
    }

    /// Emit a message that suggests something to the user.
    fn help(&self, msg: impl Into<String>) {
        self.struct_help(msg).emit()
    }

    /// Emit a message that is severe enough that it causes the policy to fail
    /// with a source code span.
    fn span_error(&self, msg: impl Into<String>, span: Span) {
        self.struct_span_error(span, msg).emit()
    }

    /// Emit a message that indicates to the user that the policy might be
    /// fraudulent but could be correct. Includes a source code span.
    fn span_warning(&self, msg: impl Into<String>, span: Span) {
        self.struct_span_warning(span, msg).emit()
    }

    /// Emit a message that provides additional information to the user.
    fn span_note(&self, msg: impl Into<String>, span: Span) {
        self.struct_span_note(span, msg).emit()
    }

    /// Emit a message that suggests something to the user.
    fn span_help(&self, msg: impl Into<String>, span: Span) {
        self.struct_span_help(span, msg).emit()
    }

    /// Initialize a diagnostic builder for an error with the span of a graph
    /// node.
    ///
    /// This will fail the policy.
    fn struct_node_error(
        &self,
        node: GlobalNode,
        msg: impl Into<String>,
    ) -> DiagnosticBuilder<'_, Self> {
        struct_node_diagnostic(self, node, Severity::Error, msg)
    }

    /// Initialize a diagnostic builder for an error with the span of a graph
    /// node.
    ///
    /// This will not fail the policy.
    fn struct_node_warning(
        &self,
        node: GlobalNode,
        msg: impl Into<String>,
    ) -> DiagnosticBuilder<'_, Self> {
        struct_node_diagnostic(self, node, Severity::Warning, msg)
    }

    /// Initialize a diagnostic builder for an note with the span of a graph
    /// node.
    fn struct_node_note(
        &self,
        node: GlobalNode,
        msg: impl Into<String>,
    ) -> DiagnosticBuilder<'_, Self> {
        struct_node_diagnostic(self, node, Severity::Note, msg)
    }

    /// Initialize a diagnostic builder for an help message with the span of a graph
    /// node.
    fn struct_node_help(
        &self,
        node: GlobalNode,
        msg: impl Into<String>,
    ) -> DiagnosticBuilder<'_, Self> {
        struct_node_diagnostic(self, node, Severity::Help, msg)
    }

    /// Emit an error, failing the policy, with the span of a graph node.
    fn node_error(&self, node: GlobalNode, msg: impl Into<String>) {
        self.struct_node_error(node, msg).emit()
    }

    /// Emit an warning, that does not fail the policy, with the span of a graph
    /// node.
    fn node_warning(&self, node: GlobalNode, msg: impl Into<String>) {
        self.struct_node_warning(node, msg).emit()
    }

    /// Emit a note with the span of a graph node.
    fn node_note(&self, node: GlobalNode, msg: impl Into<String>) {
        self.struct_node_note(node, msg).emit()
    }

    /// Emit a help message with the span of a graph node.
    fn node_help(&self, node: GlobalNode, msg: impl Into<String>) {
        self.struct_node_note(node, msg).emit()
    }
}

fn highlighted_node_span(ctx: &RootContext, node: GlobalNode) -> HighlightedSpan {
    let node_span = node.get_location(ctx);
    let stmt_span = &ctx.instruction_at_node(node).span;
    if stmt_span.contains(node_span) {
        HighlightedSpan::new(stmt_span.clone(), node_span.start, node_span.end)
    } else {
        stmt_span.clone().into()
    }
}

fn struct_node_diagnostic<B: HasDiagnosticsBase + ?Sized>(
    base: &B,
    node: GlobalNode,
    severity: Severity,
    msg: impl Into<String>,
) -> DiagnosticBuilder<'_, B> {
    DiagnosticBuilder::init(
        msg.into(),
        severity,
        Some(highlighted_node_span(base.as_ctx(), node)),
        base,
    )
}

const TAB_SIZE: usize = 4;

fn line_length_while(s: &str, mut cont: impl FnMut(char) -> bool) -> usize {
    s.chars()
        .fold((false, 0), |(found, num), c| {
            if found || !cont(c) {
                (true, num)
            } else {
                let more = if c == '\t' { TAB_SIZE } else { 1 };
                (false, num + more)
            }
        })
        .1
}

#[cfg(test)]
mod tests {
    use crate::diagnostics::{line_length_while, TAB_SIZE};

    #[test]
    fn test_line_length() {
        assert_eq!(line_length_while("  ", |_| true), 2);
        assert_eq!(line_length_while("  . ", |_| true), 4);
        assert_eq!(line_length_while("  . ", char::is_whitespace), 2);
        assert_eq!(line_length_while("\t", |_| true), TAB_SIZE);
        assert_eq!(line_length_while("\t . ", |_| true), TAB_SIZE + 3);
        assert_eq!(line_length_while(" . \t", |_| true), TAB_SIZE + 3);
        assert_eq!(line_length_while("\t. ", char::is_whitespace), TAB_SIZE);
        assert_eq!(
            line_length_while("\t \t. ", char::is_whitespace),
            2 * TAB_SIZE + 1
        );
    }
}

impl<T: HasDiagnosticsBase> Diagnostics for T {}

/// A context for a named policy.
///
/// You may call any method and access any field defined on [`Context`]. In
/// addition all diagnostics messages emitted from this struct will carry the
/// name of the policy.
///
/// See the [module level documentation][self] for more information on
/// diagnostic context management.
pub struct PolicyContext {
    name: Identifier,
    inner: Arc<dyn HasDiagnosticsBase>,
}

impl std::ops::Deref for PolicyContext {
    type Target = RootContext;
    fn deref(&self) -> &Self::Target {
        self.as_ctx()
    }
}

impl PolicyContext {
    /// Add a named combinator to the diagnostic context.
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_combinator<A>(
        self: Arc<Self>,
        name: impl Into<Identifier>,
        computation: impl FnOnce(Arc<CombinatorContext>) -> A,
    ) -> A {
        computation(Arc::new(CombinatorContext {
            name: name.into(),
            inner: self,
        }))
    }

    /// Run the computation in the diagnostic context of this controller
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_controller<A>(
        self: Arc<Self>,
        id: Endpoint,
        policy: impl FnOnce(Arc<ControllerContext>) -> A,
    ) -> A {
        policy(Arc::new(ControllerContext {
            id,
            inner: self as Arc<_>,
        }))
    }

    /// Iterate over all defined controllers as contexts
    pub fn controller_contexts(self: &Arc<Self>) -> impl Iterator<Item = Arc<ControllerContext>> {
        ControllerContext::for_all(self.clone() as Arc<_>)
    }
}

impl HasDiagnosticsBase for PolicyContext {
    fn record(&self, mut diagnostic: Diagnostic) {
        diagnostic
            .context
            .push(Identifier::new_intern(&format!("[policy: {}]", self.name)));
        self.inner.record(diagnostic)
    }

    fn as_ctx(&self) -> &RootContext {
        self.inner.as_ctx()
    }
}

/// A context for controllers
///
/// You may call any method and access any field defined on [`Context`]. In
/// addition all diagnostics messages emitted from this struct will carry the
/// name of the controller.
///
/// See the [module level documentation][self] for more information on
/// diagnostic context management.
pub struct ControllerContext {
    id: Endpoint,
    inner: Arc<dyn HasDiagnosticsBase>,
}

impl std::ops::Deref for ControllerContext {
    type Target = RootContext;
    fn deref(&self) -> &Self::Target {
        self.as_ctx()
    }
}

impl ControllerContext {
    /// Add a named combinator to the diagnostic context.
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_combinator<A>(
        self: Arc<Self>,
        name: impl Into<Identifier>,
        computation: impl FnOnce(Arc<CombinatorContext>) -> A,
    ) -> A {
        computation(Arc::new(CombinatorContext {
            name: name.into(),
            inner: self,
        }))
    }

    /// Add a policy to the diagnostic context.
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_policy<A>(
        self: Arc<Self>,
        name: impl Into<Identifier>,
        policy: impl FnOnce(Arc<PolicyContext>) -> A,
    ) -> A {
        policy(Arc::new(PolicyContext {
            name: name.into(),
            inner: self as Arc<_>,
        }))
    }

    /// Access the id for the controller of this context
    pub fn id(&self) -> Endpoint {
        self.id
    }

    /// Access the current controller contents
    pub fn current(&self) -> &SPDG {
        &self.inner.as_ctx().desc().controllers[&self.id]
    }

    fn for_all(ctx: Arc<dyn HasDiagnosticsBase>) -> impl Iterator<Item = Arc<Self>> {
        ctx.as_ctx()
            .desc()
            .controllers
            .keys()
            .copied()
            .collect::<Vec<_>>()
            .into_iter()
            .map(move |id| Self {
                id,
                inner: ctx.clone(),
            })
            .map(Arc::new)
    }
}

impl HasDiagnosticsBase for ControllerContext {
    fn record(&self, mut diagnostic: Diagnostic) {
        let ctrl = &self.as_ctx().desc().controllers[&self.id];
        diagnostic.context.push(Identifier::new_intern(&format!(
            "[controller: {}]",
            DisplayPath::from(&ctrl.path)
        )));
        self.inner.record(diagnostic)
    }

    fn as_ctx(&self) -> &RootContext {
        self.inner.as_ctx()
    }
}

impl Context for ControllerContext {
    fn root(&self) -> &RootContext {
        self.as_ctx()
    }

    fn marked_nodes(&self, marker: crate::Marker) -> impl Iterator<Item = GlobalNode> + '_ {
        self.root()
            .marked_nodes(marker)
            .filter(|n| n.controller_id() == self.id)
    }

    fn nodes_marked_via_type(
        &self,
        marker: crate::Marker,
    ) -> impl Iterator<Item = GlobalNode> + '_ {
        self.root()
            .nodes_marked_via_type(marker)
            .filter(|n| n.controller_id() == self.id)
    }

    fn nodes_marked_any_way(&self, marker: crate::Marker) -> impl Iterator<Item = GlobalNode> + '_ {
        self.root()
            .nodes_marked_any_way(marker)
            .filter(|n| n.controller_id() == self.id)
    }
}

/// A context for combinators.
///
/// You may call any method and access any field defined on [`Context`]. In
/// addition all diagnostics messages emitted from this struct will carry the
/// name of the combinator.
///
/// See the [module level documentation][self] for more information on
/// diagnostic context management.
pub struct CombinatorContext {
    name: Identifier,
    inner: Arc<dyn HasDiagnosticsBase>,
}

impl std::ops::Deref for CombinatorContext {
    type Target = RootContext;
    fn deref(&self) -> &Self::Target {
        self.as_ctx()
    }
}

impl CombinatorContext {
    /// Nest another named combinator into the diagnostic context.
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_combinator<A>(
        self: Arc<Self>,
        name: impl Into<Identifier>,
        computation: impl FnOnce(Arc<CombinatorContext>) -> A,
    ) -> A {
        computation(Arc::new(Self::new(name, self)))
    }

    pub(crate) fn new(name: impl Into<Identifier>, inner: Arc<dyn HasDiagnosticsBase>) -> Self {
        CombinatorContext {
            name: name.into(),
            inner,
        }
    }
}

impl HasDiagnosticsBase for CombinatorContext {
    fn record(&self, mut diagnostic: Diagnostic) {
        diagnostic.context.push(self.name);
        self.inner.record(diagnostic)
    }

    fn as_ctx(&self) -> &RootContext {
        self.inner.as_ctx()
    }
}

impl RootContext {
    /// Add a policy to the diagnostic context.
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_policy<A>(
        self: Arc<Self>,
        name: impl Into<Identifier>,
        policy: impl FnOnce(Arc<PolicyContext>) -> A,
    ) -> A {
        policy(Arc::new(PolicyContext {
            name: name.into(),
            inner: self as Arc<_>,
        }))
    }

    /// Run the computation in the diagnostic context of this controller
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_controller<A>(
        self: Arc<Self>,
        id: Endpoint,
        policy: impl FnOnce(Arc<ControllerContext>) -> A,
    ) -> A {
        policy(Arc::new(ControllerContext {
            id,
            inner: self as Arc<_>,
        }))
    }

    /// Nest another named combinator into the diagnostic context.
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_combinator<A>(
        self: Arc<Self>,
        name: impl Into<Identifier>,
        computation: impl FnOnce(Arc<CombinatorContext>) -> A,
    ) -> A {
        computation(Arc::new(CombinatorContext::new(name, self)))
    }

    /// Iterate over all defined controllers as contexts
    pub fn controller_contexts(self: &Arc<Self>) -> impl Iterator<Item = Arc<ControllerContext>> {
        ControllerContext::for_all(self.clone() as Arc<_>)
    }
}

/// Base database of emitted diagnostics.
#[derive(Debug, Default)]
pub(crate) struct DiagnosticsRecorder(std::sync::Mutex<IndexMap<Diagnostic, ()>>);

struct DisplayDiagnostic<'a>(&'a Diagnostic);

impl<'a> std::fmt::Display for DisplayDiagnostic<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.write(f)
    }
}

impl DiagnosticsRecorder {
    /// Emit queued diagnostics, draining the internal queue of diagnostics.
    ///
    /// A return `true` means the program may continue, on `false` it should be
    /// aborted.
    pub(crate) fn emit(&self, mut w: impl Write) -> std::io::Result<bool> {
        let w = &mut w;
        let mut can_continue = true;
        for (diag, ()) in self.0.lock().unwrap().drain(..) {
            writeln!(w, "{}", DisplayDiagnostic(&diag))?;
            can_continue &= !diag.children.iter().any(|c| c.severity.must_abort());
        }
        Ok(can_continue)
    }
}

impl HasDiagnosticsBase for RootContext {
    /// Record a diagnostic message.
    fn record(&self, diagnostic: Diagnostic) {
        self.diagnostics.0.lock().unwrap().insert(diagnostic, ());
    }

    fn as_ctx(&self) -> &RootContext {
        self
    }
}
