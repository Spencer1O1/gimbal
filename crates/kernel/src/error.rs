//! Kernel error types shared across modules.
//!
//! Distinguishes user-facing construction failures from internal
//! [`KernelFault`]s. Checking, equality, and model faults land with
//! those modules.

use std::fmt;

/// Why a candidate identifier was rejected as a [`crate::name::Name`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidNameReason {
    /// The input was empty.
    Empty,
    /// The first character is not an ASCII letter or underscore.
    InvalidStart(char),
    /// A later character is not an ASCII letter, digit, or underscore.
    InvalidChar { position: usize, ch: char },
}

/// A string failed Phase 0 name validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvalidName {
    input: String,
    reason: InvalidNameReason,
}

impl InvalidName {
    pub(crate) fn new(input: impl Into<String>, reason: InvalidNameReason) -> Self {
        Self {
            input: input.into(),
            reason,
        }
    }

    /// The rejected input text.
    pub fn input(&self) -> &str {
        &self.input
    }

    /// Structured rejection reason.
    pub fn reason(&self) -> &InvalidNameReason {
        &self.reason
    }
}

impl fmt::Display for InvalidName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.reason {
            InvalidNameReason::Empty => write!(f, "name must be non-empty"),
            InvalidNameReason::InvalidStart(ch) => write!(
                f,
                "name {:?} must start with an ASCII letter or underscore, found {ch:?}",
                self.input
            ),
            InvalidNameReason::InvalidChar { position, ch } => write!(
                f,
                "name {:?} has invalid character {ch:?} at byte index {position}",
                self.input
            ),
        }
    }
}

impl std::error::Error for InvalidName {}

/// Internal kernel inconsistency.
///
/// This is not a user typing or construction error. Ordinary API failures
/// should use dedicated error types; a [`KernelFault`] means an invariant
/// the trusted kernel assumed was broken.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelFault {
    message: &'static str,
}

impl KernelFault {
    /// Construct a fault for a broken kernel invariant.
    ///
    /// Not yet emitted by production paths; retained for trusted constructors.
    #[allow(dead_code)]
    pub(crate) const fn new(message: &'static str) -> Self {
        Self { message }
    }

    /// Static description of the broken invariant.
    pub const fn message(&self) -> &'static str {
        self.message
    }
}

impl fmt::Display for KernelFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "kernel fault: {}", self.message)
    }
}

impl std::error::Error for KernelFault {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_name_display_mentions_input() {
        let err = InvalidName::new("1x", InvalidNameReason::InvalidStart('1'));
        let text = err.to_string();
        assert!(text.contains("1x"));
        assert!(text.contains('1'));
    }

    #[test]
    fn kernel_fault_display_prefixes_message() {
        let fault = KernelFault::new("object missing signature context");
        assert_eq!(
            fault.to_string(),
            "kernel fault: object missing signature context"
        );
    }
}
