//! Validated names for signature bases and generators.
//!
//! Phase 0 builder API grammar (provisional, not a forever Unicode policy):
//! non-empty ASCII identifiers `[A-Za-z_][A-Za-z0-9_]*`.
//! Surface-language naming may widen later; resolved kernel identity remains typed IDs.

use std::fmt;

use crate::error::{InvalidName, InvalidNameReason};

/// A validated base or generator name.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Name(String);

impl Name {
    /// Validate and wrap `text` as a [`Name`].
    ///
    /// Accepted form: non-empty ASCII identifier
    /// `[A-Za-z_][A-Za-z0-9_]*`.
    pub fn new(text: impl AsRef<str>) -> Result<Self, InvalidName> {
        let text = text.as_ref();
        validate(text)?;
        Ok(Self(text.to_owned()))
    }

    /// Borrow the underlying text.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl TryFrom<&str> for Name {
    type Error = InvalidName;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl TryFrom<String> for Name {
    type Error = InvalidName;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        validate(&value)?;
        Ok(Self(value))
    }
}

fn validate(text: &str) -> Result<(), InvalidName> {
    let mut chars = text.char_indices();
    let Some((start_index, start)) = chars.next() else {
        return Err(InvalidName::new(text, InvalidNameReason::Empty));
    };
    debug_assert_eq!(start_index, 0);

    if !is_name_start(start) {
        return Err(InvalidName::new(
            text,
            InvalidNameReason::InvalidStart(start),
        ));
    }

    for (position, ch) in chars {
        if !is_name_continue(ch) {
            return Err(InvalidName::new(
                text,
                InvalidNameReason::InvalidChar { position, ch },
            ));
        }
    }

    Ok(())
}

const fn is_name_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

const fn is_name_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::InvalidNameReason;

    #[test]
    fn accepts_ascii_identifiers() {
        for text in ["Number", "two", "add", "_hidden", "a1", "A_B"] {
            let name = Name::new(text).expect("valid name");
            assert_eq!(name.as_str(), text);
            assert_eq!(name.to_string(), text);
        }
    }

    #[test]
    fn rejects_empty() {
        let err = Name::new("").expect_err("empty");
        assert_eq!(err.reason(), &InvalidNameReason::Empty);
    }

    #[test]
    fn rejects_invalid_start() {
        let err = Name::new("1number").expect_err("digit start");
        assert_eq!(err.reason(), &InvalidNameReason::InvalidStart('1'));
    }

    #[test]
    fn rejects_invalid_continue() {
        let err = Name::new("foo-bar").expect_err("hyphen");
        assert_eq!(
            err.reason(),
            &InvalidNameReason::InvalidChar {
                position: 3,
                ch: '-'
            }
        );
    }

    #[test]
    fn rejects_non_ascii() {
        let err = Name::new("café").expect_err("non-ascii");
        assert!(matches!(
            err.reason(),
            InvalidNameReason::InvalidChar { ch: 'é', .. }
        ));
    }

    #[test]
    fn try_from_string_accepts_owned_input() {
        let name = Name::try_from(String::from("UnitLike")).expect("valid");
        assert_eq!(name.as_str(), "UnitLike");
    }
}
