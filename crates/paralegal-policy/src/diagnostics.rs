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
//! fn my_check(ctx: Arc<Context>) {
//!     ctx.named_policy("cannot escape", |ctx| {
//!         let result_1 = ctx.named_combinator("collect something", |ctx| {
//!             /* actual computation */
//!             assert_error!(ctx, 1 + 2 == 4, "Oh oh, fail!");
//!             true
//!         });
//!         let result_2 = ctx.named_combinator("reach something", |ctx| {
//!             assert_warning!(ctx, 1 - 3 == 0, "maybe wrong?");
//!             false
//!         })
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
//! [`report`][crate::AlwaysHappensBefore::report] functions.

#![allow(clippy::arc_with_non_send_sync)]

use colored::*;
use std::rc::Rc;
use std::{io::Write, sync::Arc};

use paralegal_spdg::{GlobalNode, Identifier, SPDG};

use crate::{Context, ControllerId};

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
#[derive(Debug, Clone, Copy)]
pub enum Severity {
    /// This indicates that the policy failed.
    Fail,
    /// This could indicate that the policy does not operate as intended.
    Warning,
    /// Additional information for a diagnostic
    Note,
    /// Some helpful hint
    Help,
}

impl Severity {
    fn must_abort(self) -> bool {
        matches!(self, Severity::Fail)
    }
}

/// Context provided to [`HasDiagnosticsBase::record`].
pub type DiagnosticContextStack = Vec<String>;

#[derive(Debug)]
struct Diagnostic {
    message: String,
    severity: Severity,
    context: DiagnosticContextStack,
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
    fn record(&self, msg: String, severity: Severity, context: DiagnosticContextStack);

    /// Access to [`Context`], usually also available via [`std::ops::Deref`].
    fn as_ctx(&self) -> &Context;
}

impl<T: HasDiagnosticsBase> HasDiagnosticsBase for Arc<T> {
    fn record(&self, msg: String, severity: Severity, context: DiagnosticContextStack) {
        let t: &T = self.as_ref();
        t.record(msg, severity, context)
    }

    fn as_ctx(&self) -> &Context {
        self.as_ref().as_ctx()
    }
}

impl<T: HasDiagnosticsBase> HasDiagnosticsBase for &'_ T {
    fn as_ctx(&self) -> &Context {
        (*self).as_ctx()
    }

    fn record(&self, msg: String, severity: Severity, context: DiagnosticContextStack) {
        (*self).record(msg, severity, context)
    }
}

impl<T: HasDiagnosticsBase> HasDiagnosticsBase for Rc<T> {
    fn as_ctx(&self) -> &Context {
        (**self).as_ctx()
    }

    fn record(&self, msg: String, severity: Severity, context: DiagnosticContextStack) {
        (**self).record(msg, severity, context)
    }
}

/// User-facing methods to emit diagnostics.
///
/// This is how any types implementing [`HasDiagnosticsBase`] should actually be
/// used.
pub trait Diagnostics: HasDiagnosticsBase {
    /// Emit a message that is severe enough that it causes the policy to fail.
    fn error(&self, msg: impl Into<String>) {
        self.record(msg.into(), Severity::Fail, vec![])
    }

    /// Emit a message that indicates to the user that the policy might be
    /// fraudulent but could be correct.
    fn warning(&self, msg: impl Into<String>) {
        self.record(msg.into(), Severity::Warning, vec![])
    }

    /// Emit a message that provides additional information to the user.
    fn note(&self, msg: impl Into<String>) {
        self.record(msg.into(), Severity::Note, vec![])
    }

    /// Emit a message that suggests something to the user.
    fn hint(&self, msg: impl Into<String>) {
        self.record(msg.into(), Severity::Help, vec![])
    }

    /// Prints a diagnostic message and the source code that corresponds to the
    /// given node.
    ///
    /// The severity governs the severity of the emitted message (the same as
    /// e.g. [`Self::error`]) and the coloring of the span information.
    fn node_diagnostic(
        &self,
        node: GlobalNode,
        msg: impl Into<String>,
        severity: Severity,
    ) -> anyhow::Result<()> {
        use std::fmt::Write;
        let (diag_type, coloring) = match severity {
            Severity::Fail => ("error", (|s| s.red()) as fn(&str) -> ColoredString),
            Severity::Warning => ("warning", (|s: &str| s.yellow()) as _),
            Severity::Note => ("note", (|s: &str| s.blue()) as _),
            Severity::Help => ("help", (|s: &str| s.green()) as _),
        };

        let mut s = String::new();
        macro_rules! println {
            ($($t:tt)*) => {
                writeln!(s, $($t)*)?;
            };
        }
        use std::io::BufRead;
        let node_kind = self.as_ctx().node_info(node).kind;

        let src_loc = &self.as_ctx().get_location(node);

        let max_line_len = std::cmp::max(
            src_loc.start_line.to_string().len(),
            src_loc.end_line.to_string().len(),
        );

        println!("{}: {}", coloring(diag_type), msg.into());
        let tab: String = " ".repeat(max_line_len);
        println!(
            "{}{} {}:{}:{} ({node_kind})",
            tab,
            "-->".blue(),
            src_loc.source_file.file_path,
            src_loc.start_line,
            src_loc.start_col,
        );
        println!("{} {}", tab, "|".blue());
        let lines =
            std::io::BufReader::new(std::fs::File::open(&src_loc.source_file.abs_file_path)?)
                .lines()
                .skip(src_loc.start_line - 1)
                .take(src_loc.end_line - src_loc.start_line + 1)
                .enumerate();
        for (i, line) in lines {
            let line_content: String = line?;
            let line_num = src_loc.start_line + i;
            let end: usize = if line_num == src_loc.end_line {
                line_length_while(&line_content[0..src_loc.end_col - 1], |_| true)
            } else {
                line_length_while(&line_content, |_| true)
            };
            let start: usize = if line_num == src_loc.start_line {
                line_length_while(&line_content[0..src_loc.start_col - 1], |_| true)
            } else {
                line_length_while(&line_content, char::is_whitespace)
            };
            let tab_len = max_line_len - line_num.to_string().len();

            println!(
                "{}{} {} {}",
                " ".repeat(tab_len),
                &line_num.to_string().blue(),
                "|".blue(),
                line_content.replace('\t', &" ".repeat(TAB_SIZE))
            );
            println!(
                "{} {} {}{}",
                tab,
                "|".blue(),
                " ".repeat(start),
                coloring(&"^".repeat(end - start))
            );
        }
        println!("{} {}", tab, "|".blue());
        self.record(s, severity, vec![]);
        Ok(())
    }

    /// Prints an error message for a problematic node
    fn print_node_error(&self, node: GlobalNode, msg: &str) -> anyhow::Result<()> {
        self.node_diagnostic(node, msg, Severity::Fail)
    }

    /// Prints a warning message for a problematic node
    fn print_node_warning(&self, node: GlobalNode, msg: &str) -> anyhow::Result<()> {
        self.node_diagnostic(node, msg, Severity::Warning)
    }

    /// Prints a note for a problematic node
    fn print_node_note(&self, node: GlobalNode, msg: &str) -> anyhow::Result<()> {
        self.node_diagnostic(node, msg, Severity::Note)
    }

    /// Print a hint with a node
    fn print_node_hint(&self, node: GlobalNode, msg: &str) -> anyhow::Result<()> {
        self.node_diagnostic(node, msg, Severity::Help)
    }
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
    type Target = Context;
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
        id: ControllerId,
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
    fn record(&self, msg: String, severity: Severity, mut context: DiagnosticContextStack) {
        context.push(format!("[policy: {}]", self.name));
        self.inner.record(msg, severity, context)
    }

    fn as_ctx(&self) -> &Context {
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
    id: ControllerId,
    inner: Arc<dyn HasDiagnosticsBase>,
}

impl std::ops::Deref for ControllerContext {
    type Target = Context;
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
    pub fn id(&self) -> ControllerId {
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
    fn record(&self, msg: String, severity: Severity, mut context: DiagnosticContextStack) {
        let name = self.as_ctx().desc().controllers[&self.id].name;
        context.push(format!("[controller: {}]", name));
        self.inner.record(msg, severity, context)
    }

    fn as_ctx(&self) -> &Context {
        self.inner.as_ctx()
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
    type Target = Context;
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
    fn record(&self, msg: String, severity: Severity, mut context: DiagnosticContextStack) {
        context.push(format!("{}", self.name));
        self.inner.record(msg, severity, context)
    }

    fn as_ctx(&self) -> &Context {
        self.inner.as_ctx()
    }
}

impl Context {
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
        id: ControllerId,
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
pub(crate) struct DiagnosticsRecorder(std::sync::Mutex<Vec<Diagnostic>>);

impl DiagnosticsRecorder {
    /// Emit queued diagnostics, draining the internal queue of diagnostics.
    ///
    /// A return `true` means the program may continue, on `false` it should be
    /// aborted.
    pub(crate) fn emit(&self, mut w: impl Write) -> std::io::Result<bool> {
        let w = &mut w;
        let mut can_continue = true;
        for diag in self.0.lock().unwrap().drain(..) {
            for ctx in diag.context.iter().rev() {
                write!(w, "{ctx} ")?;
            }
            writeln!(w, "{}", diag.message)?;
            can_continue &= !diag.severity.must_abort();
        }
        Ok(can_continue)
    }
}

impl HasDiagnosticsBase for Context {
    /// Record a diagnostic message.
    fn record(&self, message: String, severity: Severity, context: DiagnosticContextStack) {
        self.diagnostics.0.lock().unwrap().push(Diagnostic {
            message,
            severity,
            context,
        })
    }

    fn as_ctx(&self) -> &Context {
        self
    }
}
