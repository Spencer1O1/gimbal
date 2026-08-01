//! Phase 0 structural semantic kernel.
//!
//! Domain modules will land in the Immediate Coding Order starting at `id`.

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
}
