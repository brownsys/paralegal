use std::io::Write;

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

#[derive(Debug, Clone, Copy)]
pub enum Severity {
    Fail,
    Warning,
}

impl Severity {
    fn must_abort(self) -> bool {
        matches!(self, Severity::Fail)
    }
}

#[derive(Debug)]
struct Diagnostic {
    message: DiagnosticMessage,
    severity: Severity,
}

#[derive(Debug, Default)]
pub struct Diagnostics(std::sync::Mutex<Vec<Diagnostic>>);

impl Diagnostics {
    /// Record a diagnostic message.
    pub fn record(&self, msg: impl Into<DiagnosticMessage>, severity: Severity) {
        self.0.lock().unwrap().push(Diagnostic {
            message: msg.into(),
            severity,
        })
    }

    /// Emit queued diagnostics, draining the internal queue of diagnostics.
    ///
    /// A return `true` means the program may continue, on `false` it should be
    /// aborted.
    pub fn emit(&self, mut w: impl Write) -> std::io::Result<bool> {
        let w = &mut w;
        let mut can_continue = true;
        for diag in self.0.lock().unwrap().drain(..) {
            write!(w, "{}", diag.message)?;
            can_continue |= diag.severity.must_abort();
        }
        Ok(can_continue)
    }
}
