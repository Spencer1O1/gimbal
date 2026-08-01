//! Phase 0 structural semantic kernel.
//!
//! Immediate coding order continues after the identity leaf modules:
//! `object_expr`, `object`, `signature`, then terms and checking.

mod error;
mod id;
mod name;

pub use error::{InvalidName, InvalidNameReason, KernelFault};
pub use id::{BaseId, GeneratorId, SignatureContextId, SignatureFingerprint};
pub use name::Name;

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
