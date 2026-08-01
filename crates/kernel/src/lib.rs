//! Phase 0 structural semantic kernel.
//!
//! Next milestone track: Lean core syntax (Milestone 4). Rust simplifier /
//! equality follow later milestones.

mod check;
mod error;
mod format;
mod id;
mod morphism;
mod name;
mod object;
mod object_expr;
mod signature;
mod term;

pub use check::check;
pub use error::{
    CheckError, FormatError, InvalidName, InvalidNameReason, KernelFault, ObjectError,
    SignatureError, TermError,
};
pub use format::{
    format_arrow, format_morphism, format_object, format_term, format_typed_morphism,
};
pub use id::{BaseId, GeneratorId, SignatureContextId, SignatureFingerprint};
pub use morphism::{Morphism, MorphismKind};
pub use name::Name;
pub use object::{Object, ObjectKind};
pub use object_expr::ObjectExpr;
pub use signature::{GeneratorDecl, Signature, SignatureBuilder};
pub use term::{Term, TermKind};

/// Placeholder export so the CLI can depend on a public kernel API.
pub fn kernel_version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kernel_version_is_present() {
        assert!(!kernel_version().is_empty());
    }

    #[test]
    fn name_round_trips_through_crate_root() {
        let name = Name::new("Number").expect("valid");
        assert_eq!(name.as_str(), "Number");
    }
}
