//! Typed identifiers and signature identity handles.
//!
//! [`BaseId`] and [`GeneratorId`] are dense indices assigned by the signature
//! builder. [`SignatureContextId`] is an exact process-local context identity;
//! [`SignatureFingerprint`] is `SHA-256` of the canonical signature encoding.

use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

/// Resolved identity of a base object in a signature.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct BaseId(u32);

impl BaseId {
    /// Mint a dense base index. Signature construction owns allocation.
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

/// SHA-256 digest of a signature's canonical encoding.
///
/// Identical canonical contents imply equal fingerprints. Equal fingerprints
/// imply identical contents only under the standard cryptographic assumption
/// that SHA-256 collisions are infeasible. Fingerprint equality never authorizes
/// mixing IR across [`SignatureContextId`]s.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SignatureFingerprint([u8; 32]);

impl SignatureFingerprint {
    /// Wrap a SHA-256 digest.
    pub(crate) const fn from_sha256(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Raw 32-byte SHA-256 digest.
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl fmt::Debug for SignatureFingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SignatureFingerprint(0x")?;
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for SignatureFingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
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
    fn fingerprints_compare_by_digest_bytes() {
        let mut left_bytes = [0u8; 32];
        left_bytes[0] = 0xab;
        left_bytes[1] = 0xcd;
        let right_bytes = left_bytes;
        let mut other_bytes = left_bytes;
        other_bytes[1] = 0xce;

        let left = SignatureFingerprint::from_sha256(left_bytes);
        let right = SignatureFingerprint::from_sha256(right_bytes);
        let other = SignatureFingerprint::from_sha256(other_bytes);
        assert_eq!(left, right);
        assert_ne!(left, other);
        assert_eq!(left.as_bytes().len(), 32);
        assert!(left.to_string().starts_with("abcd"));
        assert!(format!("{left:?}").contains("SignatureFingerprint(0xabcd"));
    }
}
