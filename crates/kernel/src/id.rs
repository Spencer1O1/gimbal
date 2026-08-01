//! Typed identifiers and signature identity handles.
//!
//! [`BaseId`] and [`GeneratorId`] are dense indices assigned by the signature
//! builder. [`SignatureContextId`] is an exact process-local context identity;
//! [`SignatureFingerprint`] is a stable digest of canonical signature contents.
//!
//! The fingerprint encoding and hash algorithm remain open (see Obsidian Open
//! Questions). This module only owns the opaque handle type.

use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

/// Resolved identity of a base object in a signature.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct BaseId(u32);

impl BaseId {
    /// Mint a dense base index. Signature construction owns allocation.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) const fn new(raw: u32) -> Self {
        Self(raw)
    }

    /// Dense index assigned when the signature was built.
    pub const fn as_u32(self) -> u32 {
        self.0
    }
}

impl fmt::Display for BaseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "base#{}", self.0)
    }
}

/// Resolved identity of a generating morphism in a signature.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct GeneratorId(u32);

impl GeneratorId {
    /// Mint a dense generator index. Signature construction owns allocation.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) const fn new(raw: u32) -> Self {
        Self(raw)
    }

    /// Dense index assigned when the signature was built.
    pub const fn as_u32(self) -> u32 {
        self.0
    }
}

impl fmt::Display for GeneratorId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "gen#{}", self.0)
    }
}

/// Exact identity of one immutable signature context.
///
/// Values from different contexts must not be mixed in checked IR, even when
/// their [`SignatureFingerprint`]s match.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SignatureContextId(u64);

impl SignatureContextId {
    /// Allocate a fresh process-local context identity.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn fresh() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        Self(NEXT.fetch_add(1, Ordering::Relaxed))
    }

    /// Process-local raw identity (not a content hash).
    pub const fn as_u64(self) -> u64 {
        self.0
    }
}

impl fmt::Display for SignatureContextId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "sigctx#{}", self.0)
    }
}

/// Canonical fingerprint of a signature's contents.
///
/// Equality of fingerprints means identical canonical contents. It does not
/// authorize mixing IR across [`SignatureContextId`]s.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SignatureFingerprint {
    bytes: Box<[u8]>,
}

impl SignatureFingerprint {
    /// Wrap already-computed canonical digest bytes.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn new(bytes: impl Into<Box<[u8]>>) -> Self {
        Self {
            bytes: bytes.into(),
        }
    }

    /// Raw digest bytes in the chosen (future) canonical encoding.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

impl fmt::Debug for SignatureFingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SignatureFingerprint(0x")?;
        for byte in self.bytes.iter() {
            write!(f, "{byte:02x}")?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for SignatureFingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.bytes.iter() {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_ids_expose_raw_indices() {
        assert_eq!(BaseId::new(3).as_u32(), 3);
        assert_eq!(GeneratorId::new(7).as_u32(), 7);
        assert_eq!(BaseId::new(3).to_string(), "base#3");
        assert_eq!(GeneratorId::new(7).to_string(), "gen#7");
    }

    #[test]
    fn context_ids_are_unique() {
        let a = SignatureContextId::fresh();
        let b = SignatureContextId::fresh();
        assert_ne!(a, b);
        assert_ne!(a.as_u64(), 0);
    }

    #[test]
    fn fingerprints_compare_by_bytes() {
        let left = SignatureFingerprint::new([0xabu8, 0xcd]);
        let right = SignatureFingerprint::new([0xabu8, 0xcd]);
        let other = SignatureFingerprint::new([0xabu8, 0xce]);
        assert_eq!(left, right);
        assert_ne!(left, other);
        assert_eq!(left.to_string(), "abcd");
        assert_eq!(format!("{left:?}"), "SignatureFingerprint(0xabcd)");
    }
}
