//! Resolved Phase 0 objects.
//!
//! Objects are opaque [`Arc`](std::sync::Arc) handles. Equality is structural
//! within a signature context, not pointer identity.

use std::fmt;
use std::sync::Arc;

use crate::error::ObjectError;
use crate::id::{BaseId, SignatureContextId};

/// Resolved object in one signature context.
#[derive(Clone, Eq)]
pub struct Object(Arc<ObjectData>);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct ObjectData {
    signature: SignatureContextId,
    node: ObjectNode,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum ObjectNode {
    Base(BaseId),
    Unit,
    Never,
    Product(Object, Object),
    Coproduct(Object, Object),
    Exponential(Object, Object),
}

/// Borrowed view of an object's constructor and children.
#[derive(Clone, Copy, Debug)]
pub enum ObjectKind<'a> {
    Base(BaseId),
    Unit,
    Never,
    Product(&'a Object, &'a Object),
    Coproduct(&'a Object, &'a Object),
    Exponential(&'a Object, &'a Object),
}

impl Object {
    pub(crate) fn new(signature: SignatureContextId, node: ObjectNode) -> Self {
        Self(Arc::new(ObjectData { signature, node }))
    }

    /// Exact signature context this object belongs to.
    pub fn signature_context(&self) -> SignatureContextId {
        self.0.signature
    }

    /// Exhaustive constructor view.
    pub fn kind(&self) -> ObjectKind<'_> {
        match &self.0.node {
            ObjectNode::Base(id) => ObjectKind::Base(*id),
            ObjectNode::Unit => ObjectKind::Unit,
            ObjectNode::Never => ObjectKind::Never,
            ObjectNode::Product(left, right) => ObjectKind::Product(left, right),
            ObjectNode::Coproduct(left, right) => ObjectKind::Coproduct(left, right),
            ObjectNode::Exponential(domain, codomain) => ObjectKind::Exponential(domain, codomain),
        }
    }

    pub(crate) fn ensure_context(&self, expected: SignatureContextId) -> Result<(), ObjectError> {
        if self.0.signature == expected {
            Ok(())
        } else {
            Err(ObjectError::SignatureMismatch {
                expected,
                actual: self.0.signature,
            })
        }
    }
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref() == other.0.as_ref()
    }
}

impl std::hash::Hash for Object {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.as_ref().hash(state);
    }
}

impl fmt::Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Object")
            .field("signature", &self.0.signature)
            .field("node", &self.0.node)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_equality_ignores_arc_identity() {
        let ctx = SignatureContextId::fresh();
        let a = Object::new(ctx, ObjectNode::Unit);
        let b = Object::new(ctx, ObjectNode::Unit);
        assert_eq!(a, b);
        assert!(!std::sync::Arc::ptr_eq(&a.0, &b.0));
    }

    #[test]
    fn different_contexts_are_unequal() {
        let left = Object::new(SignatureContextId::fresh(), ObjectNode::Unit);
        let right = Object::new(SignatureContextId::fresh(), ObjectNode::Unit);
        assert_ne!(left, right);
    }

    #[test]
    fn products_distinguish_association() {
        let ctx = SignatureContextId::fresh();
        let unit = Object::new(ctx, ObjectNode::Unit);
        let never = Object::new(ctx, ObjectNode::Never);
        let base = Object::new(ctx, ObjectNode::Base(BaseId::new(0)));

        let left_assoc = Object::new(
            ctx,
            ObjectNode::Product(
                Object::new(ctx, ObjectNode::Product(unit.clone(), never.clone())),
                base.clone(),
            ),
        );
        let right_assoc = Object::new(
            ctx,
            ObjectNode::Product(unit, Object::new(ctx, ObjectNode::Product(never, base))),
        );
        assert_ne!(left_assoc, right_assoc);
    }
}
