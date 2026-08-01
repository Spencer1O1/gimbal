//! Kernel error types shared across modules.
//!
//! Distinguishes user-facing construction failures from internal
//! [`KernelFault`]s. Checking, equality, and model faults land with
//! those modules.

use std::fmt;

use crate::id::{BaseId, GeneratorId, SignatureContextId};
use crate::name::Name;
use crate::object::Object;

/// Why a candidate identifier was rejected as a [`crate::name::Name`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidNameReason {
    /// The input was empty.
    Empty,
    /// The first character is not an ASCII letter or underscore.
    InvalidStart(char),
    /// A later character is not an ASCII letter, digit, or underscore.
    InvalidChar { position: usize, ch: char },
    /// Byte length does not fit in `u32` (canonical encoding limit).
    TooLong,
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
            InvalidNameReason::TooLong => {
                write!(f, "name length {} exceeds u32::MAX", self.input.len())
            }
        }
    }
}

impl std::error::Error for InvalidName {}

/// Failure while building or querying a signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignatureError {
    /// A supplied identifier failed name validation.
    InvalidName(InvalidName),
    /// A base name was declared more than once.
    DuplicateBase(Name),
    /// A generator name was declared more than once.
    DuplicateGenerator(Name),
    /// A generator object expression referred to an unknown base name.
    UndeclaredBase {
        /// Generator being declared when the unknown base was found.
        generator: Name,
        /// Missing base name.
        base: Name,
    },
    /// More than `u32::MAX` bases were declared.
    TooManyBases,
    /// More than `u32::MAX` generators were declared.
    TooManyGenerators,
    /// A typed base id is outside this signature.
    InvalidBaseId(BaseId),
    /// A typed generator id is outside this signature.
    InvalidGeneratorId(GeneratorId),
}

impl fmt::Display for SignatureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidName(err) => write!(f, "{err}"),
            Self::DuplicateBase(name) => write!(f, "duplicate base name `{name}`"),
            Self::DuplicateGenerator(name) => write!(f, "duplicate generator name `{name}`"),
            Self::UndeclaredBase { generator, base } => write!(
                f,
                "generator `{generator}` refers to undeclared base `{base}`"
            ),
            Self::TooManyBases => write!(f, "too many bases (exceeds u32::MAX)"),
            Self::TooManyGenerators => write!(f, "too many generators (exceeds u32::MAX)"),
            Self::InvalidBaseId(id) => write!(f, "invalid base id {id}"),
            Self::InvalidGeneratorId(id) => write!(f, "invalid generator id {id}"),
        }
    }
}

impl std::error::Error for SignatureError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidName(err) => Some(err),
            _ => None,
        }
    }
}

impl From<InvalidName> for SignatureError {
    fn from(value: InvalidName) -> Self {
        Self::InvalidName(value)
    }
}

/// Failure while constructing resolved objects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectError {
    /// An operand belongs to a different signature context.
    SignatureMismatch {
        expected: SignatureContextId,
        actual: SignatureContextId,
    },
}

impl fmt::Display for ObjectError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SignatureMismatch { expected, actual } => write!(
                f,
                "object signature mismatch: expected {expected}, found {actual}"
            ),
        }
    }
}

impl std::error::Error for ObjectError {}

/// Failure while constructing a structurally valid [`crate::Term`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermError {
    /// An operand belongs to a different signature context.
    SignatureMismatch {
        expected: SignatureContextId,
        actual: SignatureContextId,
    },
    /// A generator id is not declared in the target signature.
    InvalidGeneratorId(GeneratorId),
}

impl fmt::Display for TermError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SignatureMismatch { expected, actual } => write!(
                f,
                "term signature mismatch: expected {expected}, found {actual}"
            ),
            Self::InvalidGeneratorId(id) => write!(f, "invalid generator id {id}"),
        }
    }
}

impl std::error::Error for TermError {}

impl TermError {
    pub(crate) fn from_object_error(err: ObjectError) -> Self {
        match err {
            ObjectError::SignatureMismatch { expected, actual } => {
                Self::SignatureMismatch { expected, actual }
            }
        }
    }
}

/// Failure while checking a [`crate::Term`] into a [`crate::Morphism`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckError {
    /// The term belongs to a different signature context than the checker signature.
    SignatureMismatch {
        expected: SignatureContextId,
        actual: SignatureContextId,
    },
    /// Composition middle objects are not structurally equal.
    ComposeMismatch {
        left_target: Object,
        right_source: Object,
    },
    /// Pairing components have different sources.
    PairSourceMismatch {
        left_source: Object,
        right_source: Object,
    },
    /// Case branches have different targets.
    CaseTargetMismatch {
        left_target: Object,
        right_target: Object,
    },
    /// Curry was applied to a morphism whose source is not a product.
    CurrySourceNotProduct { source: Object },
    /// A generator id is not declared (should be unreachable for well-formed terms).
    InvalidGeneratorId(GeneratorId),
    /// Trusted morphism construction broke an invariant.
    Kernel(KernelFault),
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SignatureMismatch { expected, actual } => write!(
                f,
                "check signature mismatch: expected {expected}, found {actual}"
            ),
            Self::ComposeMismatch {
                left_target,
                right_source,
            } => write!(
                f,
                "composition mismatch: left target {left_target:?} ≠ right source {right_source:?}"
            ),
            Self::PairSourceMismatch {
                left_source,
                right_source,
            } => write!(
                f,
                "pair source mismatch: {left_source:?} ≠ {right_source:?}"
            ),
            Self::CaseTargetMismatch {
                left_target,
                right_target,
            } => write!(
                f,
                "case target mismatch: {left_target:?} ≠ {right_target:?}"
            ),
            Self::CurrySourceNotProduct { source } => {
                write!(f, "curry source is not a product: {source:?}")
            }
            Self::InvalidGeneratorId(id) => write!(f, "invalid generator id {id}"),
            Self::Kernel(fault) => write!(f, "{fault}"),
        }
    }
}

impl std::error::Error for CheckError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Kernel(fault) => Some(fault),
            _ => None,
        }
    }
}

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

    #[test]
    fn signature_error_from_invalid_name() {
        let err = SignatureError::from(InvalidName::new("", InvalidNameReason::Empty));
        assert!(matches!(err, SignatureError::InvalidName(_)));
    }
}
