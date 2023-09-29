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
use std::{io::Write, sync::Arc};

use paralegal_spdg::{rustc_portable::DefId, Identifier};

use crate::Context;

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
            $ctx.error($msg);
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
        id: DefId,
        policy: impl FnOnce(Arc<ControllerContext>) -> A,
    ) -> A {
        policy(Arc::new(ControllerContext {
            id,
            inner: self as Arc<_>,
        }))
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
    id: DefId,
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
}

impl HasDiagnosticsBase for ControllerContext {
    fn record(&self, msg: String, severity: Severity, mut context: DiagnosticContextStack) {
        let name = self.as_ctx().desc().def_info[&self.id].name;
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
        id: DefId,
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
        computation(Arc::new(Self::new(name, self)))
    }

    pub(crate) fn new(name: impl Into<Identifier>, inner: Arc<dyn HasDiagnosticsBase>) -> Self {
        CombinatorContext {
            name: name.into(),
            inner,
        }
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
                write!(w, "[{ctx}] ")?;
            }
            writeln!(w, "{}", diag.message)?;
            can_continue |= diag.severity.must_abort();
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