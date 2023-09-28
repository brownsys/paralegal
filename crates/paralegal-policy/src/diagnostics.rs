//! Emit messages to the user running a policy.
//!
//! The diagnostics of a Paralegal policy are similar to those used in rustc. In
//! particular we use a strategy of "keep going", meaning that a policy should
//! not fail at the first error. Instead it should attempt to keep going if
//! possible and emit additional errors, as those messages are useful for the
//! user.
//!
//! This manifests for instance in [`HasDiagnosticsExt::error`]. This function
//! records a severe error that should fail the policy but it does not exit the
//! program. Instead the message is recorded and emitted later, for instance by
//! [`Context::emit_diagnostics`].
//!
//! ## Emitting Messages
//!
//! The main interface for diagnostics is the [`HasDiagnosticsExt`] trait which
//! defines the convenience functions [`error`][HasDiagnosticsExt::error] for
//! policy failures and [`warning`][HasDiagnosticsExt::warning] for indicators
//! to the user that something may be off, but not causing a policy failure. For
//! future compatibility reasons those functions work with
//! [`DiagnosticMessage`], but currently only strings can be converted into
//! those messages, so you can simply use string literals `"like this"` or
//! [`String`]s directly, for instance via [`format!`].
//!
//! We also offer two convenience macros [`assert_error!`] and
//! [`assert_warning!`] that correspond to either function. Much like
//! [`assert!`] they let you use format strings for the messages. They should be
//! used like `assert_warning!(ctx, condition, "format string", ...format
//! arguments)`. `ctx` here is anything that implements [`HasDiagnosticsExt`]
//! (see below).
//!
//! [`HasDiagnosticsExt`] is implemented directly by [`Context`] so you can use
//! `ctx.error()` or `ctx.warning()`. You may however add additional contextual
//! information about which policy or combinator is currently executing.
//! [`Context::named_policy`] returns a wrapper that can be used the same way
//! that you use [`Context`], but when [`error`][HasDiagnosticsExt::error] or
//! [`warning`][HasDiagnosticsExt::warning] is called it also appends the name
//! of the policy to you specified.
//!
//! Similarly you can use [`Context::named_combinator`] or
//! [`PolicyMsg::named_combinator`] to add context about a named combinator.
//!
//! The expected workflow is something like
//!
//! ```no_run
//! fn my_check(ctx: Arc<Context>) {
//!     ctx.named_policy("policy-1", |ctx| {
//!         let result_1 = ctx.named_combinator("compute_something", |ctx| {
//!             /* actual computation */
//!             assert_error!(ctx, "Oh oh, fail!");
//!             true
//!         });
//!         let result_2 = ctx.named_combinator("another_condition", |ctx| {
//!             assert_warning!(ctx, "maybe wrong?");
//!             false
//!         })
//!         assert_error!(result_1 || result_2, "Combination failure");
//!     })
//!
//! }
//! ```
//!
//! Note that some methods, like [`Context::always_happens_before`] add a named
//! combinator context by themselves when you use their
//! [`report`][crate::AlwaysHappensBefore::report] functions.
use std::{io::Write, sync::Arc};

use paralegal_spdg::Identifier;

use crate::Context;

/// Check the condition and emit a [`Context::error`] if it fails.
#[macro_export]
macro_rules! assert_error {
    ($ctx:expr, $cond: expr, $msg:expr $(,)?) => {
        if !$cond {
            $ctx.error($msg);
        }
    };
}

/// Check the condition and emit a [`Context::warning`] if it fails.
#[macro_export]
macro_rules! assert_warning {
    ($ctx:expr, $cond: expr, $msg:expr $(,)?) => {
        if !$cond {
            $ctx.warning($msg);
        }
    };
}

/// A message that should be delivered to the user.
///
/// At the moment only supports simple string messages, which can be created
/// using [`Into`], which is implemented for both [`String`] and `&str`.
#[derive(Debug)]
pub struct DiagnosticMessage(String);

impl From<String> for DiagnosticMessage {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl<'a> From<&'a str> for DiagnosticMessage {
    fn from(value: &'a str) -> Self {
        value.to_string().into()
    }
}

impl std::fmt::Display for DiagnosticMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// Severity of a recorded diagnostic message
#[derive(Debug, Clone, Copy)]
pub enum Severity {
    /// This indicates that the policy failed.
    Fail,
    /// This could indicate that the policy does not operate as intended.
    Warning,
}

impl Severity {
    fn must_abort(self) -> bool {
        matches!(self, Severity::Fail)
    }
}

/// Something that can be printed as part of a diagnostic message context. See
/// also [`HasDiagnostics::record`].
pub trait ContextObj: std::fmt::Display + std::fmt::Debug + Send {}
impl<T: std::fmt::Display + std::fmt::Debug + Send> ContextObj for T {}

/// Context provided to [`HasDiagnostics::record`].
pub type DiagnosticContextStack = Vec<Box<dyn ContextObj>>;

#[derive(Debug)]
struct Diagnostic {
    message: DiagnosticMessage,
    severity: Severity,
    context: DiagnosticContextStack,
}

/// Base database of emitted diagnostics.
#[derive(Debug, Default)]
pub(crate) struct Diagnostics(std::sync::Mutex<Vec<Diagnostic>>);

impl Diagnostics {
    /// Emit queued diagnostics, draining the internal queue of diagnostics.
    ///
    /// A return `true` means the program may continue, on `false` it should be
    /// aborted.
    pub(crate) fn emit(&self, mut w: impl Write) -> std::io::Result<bool> {
        let w = &mut w;
        let mut can_continue = true;
        for diag in self.0.lock().unwrap().drain(..) {
            for ctx in diag.context.iter().rev() {
                write!(w, "[{ctx}] ")?;
            }
            writeln!(w, "{}", diag.message)?;
            can_continue |= diag.severity.must_abort();
        }
        Ok(can_continue)
    }
}

impl HasDiagnostics for Context {
    /// Record a diagnostic message.
    fn record(&self, message: DiagnosticMessage, severity: Severity, context: DiagnosticContextStack) {
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

/// Low level machinery for diagnostics.
///
/// As a user you should only be using methods from [`HasDiagnosticsExt`]. It
/// may however be helpful to look at the implementors of this trait, as those
/// are also implementors of [`HasDiagnosticsExt`].
pub trait HasDiagnostics {
    /// Base function for recording new diagnostics.
    ///
    /// This should be used by implementors of new wrappers, users should use
    /// high level functions like [`Self::error`] or [`Self::warning`] instead.
    fn record(&self, msg: DiagnosticMessage, severity: Severity, context: DiagnosticContextStack);

    /// Access to [`Context`], usually also available via [`std::ops::Deref`].
    fn as_ctx(&self) -> &Context;
}

impl<T: HasDiagnostics> HasDiagnostics for Arc<T> {
    fn record(&self, msg: DiagnosticMessage, severity: Severity, context: DiagnosticContextStack) {
        let t: &T = self.as_ref();
        t.record(msg, severity, context)
    }

    fn as_ctx(&self) -> &Context {
        self.as_ref().as_ctx()
    }
}

/// User-facing methods to emit diagnostics.
///
/// This is how any types implementing [`HasDiagnostics`] should actually be
/// used.
pub trait HasDiagnosticsExt: HasDiagnostics {
    /// Emit a message that is severe enough that it causes the policy to fail.
    fn error(&self, msg: impl Into<DiagnosticMessage>) {
        self.record(msg.into(), Severity::Fail, vec![])
    }

    /// Emit a message that indicates to the user that the policy might be
    /// fraudulent but could be correct.
    fn warning(&self, msg: impl Into<DiagnosticMessage>) {
        self.record(msg.into(), Severity::Warning, vec![])
    }
}

impl<T: HasDiagnostics> HasDiagnosticsExt for T {}

/// Add a policy to the diagnostic context.
///
/// See the [module level documentation][self] for more information on
/// diagnostic context management.
pub struct PolicyMsg {
    name: Identifier,
    inner: Arc<dyn HasDiagnostics>,
}

impl std::ops::Deref for PolicyMsg {
    type Target = Context;
    fn deref(&self) -> &Self::Target {
        self.as_ctx()
    }
}

impl PolicyMsg {
    /// Add a named combinator to the diagnostic context.
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_combinator<A>(
        self: Arc<Self>,
        name: impl Into<Identifier>,
        computation: impl FnOnce(Arc<CombinatorMsg>) -> A,
    ) -> A {
        computation(Arc::new(CombinatorMsg {
            name: name.into(),
            inner: self,
        }))
    }
}

impl HasDiagnostics for PolicyMsg {
    fn record(
        &self,
        msg: DiagnosticMessage,
        severity: Severity,
        mut context: DiagnosticContextStack,
    ) {
        context.push(Box::new(format!("[policy: {}]", self.name)) as Box<_>);
        self.inner.record(msg, severity, context)
    }

    fn as_ctx(&self) -> &Context {
        self.inner.as_ctx()
    }
}

/// Add a named combinator to the diagnostic context.
///
/// See the [module level documentation][self] for more information on
/// diagnostic context management.
pub struct CombinatorMsg {
    name: Identifier,
    inner: Arc<dyn HasDiagnostics>,
}

impl std::ops::Deref for CombinatorMsg {
    type Target = Context;
    fn deref(&self) -> &Self::Target {
        self.as_ctx()
    }
}

impl CombinatorMsg {
    /// Nest another named combinator into the diagnostic context.
    ///
    /// See the [module level documentation][self] for more information on
    /// diagnostic context management.
    pub fn named_combinator<A>(
        self: Arc<Self>,
        name: impl Into<Identifier>,
        computation: impl FnOnce(Arc<CombinatorMsg>) -> A,
    ) -> A {
        computation(Arc::new(Self::new(name, self)))
    }

    pub(crate) fn new(name: impl Into<Identifier>, inner: Arc<dyn HasDiagnostics>) -> Self {
        CombinatorMsg {
            name: name.into(),
            inner,
        }
    }
}

impl HasDiagnostics for CombinatorMsg {
    fn record(
        &self,
        msg: DiagnosticMessage,
        severity: Severity,
        mut context: DiagnosticContextStack,
    ) {
        context.push(Box::new(format!("[{}]", self.name)) as Box<_>);
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
        policy: impl FnOnce(Arc<PolicyMsg>) -> A,
    ) -> A {
        policy(Arc::new(PolicyMsg {
            name: name.into(),
            inner: self as Arc<_>,
        }))
    }
}
