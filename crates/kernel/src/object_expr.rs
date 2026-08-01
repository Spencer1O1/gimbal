//! Unresolved object expressions for signature construction.
//!
//! [`ObjectExpr`] names bases by [`Name`]. The signature builder resolves
//! these into [`crate::Object`] values under one context.

use crate::name::Name;

/// Unresolved Phase 0 object syntax.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ObjectExpr {
    /// Named base object; must be declared in the signature.
    Base(Name),
    /// Terminal object.
    Unit,
    /// Initial object.
    Never,
    /// Product `A × B`.
    Product(Box<ObjectExpr>, Box<ObjectExpr>),
    /// Coproduct `A + B`.
    Coproduct(Box<ObjectExpr>, Box<ObjectExpr>),
    /// Exponential `A ⇒ B` (domain, codomain).
    Exponential(Box<ObjectExpr>, Box<ObjectExpr>),
}

impl ObjectExpr {
    /// Base object referring to `name`.
    pub fn base(name: Name) -> Self {
        Self::Base(name)
    }

    /// Terminal object.
    pub const fn unit() -> Self {
        Self::Unit
    }

    /// Initial object.
    pub const fn never() -> Self {
        Self::Never
    }

    /// Product of `left` and `right`.
    pub fn product(left: Self, right: Self) -> Self {
        Self::Product(Box::new(left), Box::new(right))
    }

    /// Coproduct of `left` and `right`.
    pub fn coproduct(left: Self, right: Self) -> Self {
        Self::Coproduct(Box::new(left), Box::new(right))
    }

    /// Exponential with domain `domain` and codomain `codomain`.
    pub fn exponential(domain: Self, codomain: Self) -> Self {
        Self::Exponential(Box::new(domain), Box::new(codomain))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructors_build_expected_shape() {
        let number = ObjectExpr::base(Name::new("Number").expect("valid"));
        let expr = ObjectExpr::product(ObjectExpr::unit(), number.clone());
        assert_eq!(
            expr,
            ObjectExpr::Product(Box::new(ObjectExpr::Unit), Box::new(number))
        );
    }
}
