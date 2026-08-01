//! Explicit, potentially ill-typed core terms.
//!
//! Constructors enforce structural validity and signature-context consistency.
//! They do not enforce categorical typing — that is [`crate::check`]'s job.

use std::fmt;
use std::sync::Arc;

use crate::error::TermError;
use crate::id::{GeneratorId, SignatureContextId};
use crate::object::Object;
use crate::signature::Signature;

/// Resolved explicit term under one signature context.
#[derive(Clone, Eq)]
pub struct Term(Arc<TermData>);

#[derive(Clone, PartialEq, Eq, Debug)]
struct TermData {
    signature: SignatureContextId,
    node: TermNode,
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum TermNode {
    Generator(GeneratorId),
    Id(Object),
    Compose(Term, Term),
    Discard(Object),
    Absurd(Object),
    First(Object, Object),
    Second(Object, Object),
    Pair(Term, Term),
    Left(Object, Object),
    Right(Object, Object),
    Case(Term, Term),
    Curry(Term),
    Eval(Object, Object),
}

/// Borrowed view of a term's constructor and children.
#[derive(Clone, Copy, Debug)]
pub enum TermKind<'a> {
    Generator(GeneratorId),
    Id(&'a Object),
    Compose(&'a Term, &'a Term),
    Discard(&'a Object),
    Absurd(&'a Object),
    First(&'a Object, &'a Object),
    Second(&'a Object, &'a Object),
    Pair(&'a Term, &'a Term),
    Left(&'a Object, &'a Object),
    Right(&'a Object, &'a Object),
    Case(&'a Term, &'a Term),
    Curry(&'a Term),
    Eval(&'a Object, &'a Object),
}

impl Term {
    fn new(signature: SignatureContextId, node: TermNode) -> Self {
        Self(Arc::new(TermData { signature, node }))
    }

    /// Exact signature context this term belongs to.
    pub fn signature_context(&self) -> SignatureContextId {
        self.0.signature
    }

    /// Exhaustive constructor view.
    pub fn kind(&self) -> TermKind<'_> {
        match &self.0.node {
            TermNode::Generator(id) => TermKind::Generator(*id),
            TermNode::Id(object) => TermKind::Id(object),
            TermNode::Compose(left, right) => TermKind::Compose(left, right),
            TermNode::Discard(object) => TermKind::Discard(object),
            TermNode::Absurd(object) => TermKind::Absurd(object),
            TermNode::First(left, right) => TermKind::First(left, right),
            TermNode::Second(left, right) => TermKind::Second(left, right),
            TermNode::Pair(left, right) => TermKind::Pair(left, right),
            TermNode::Left(left, right) => TermKind::Left(left, right),
            TermNode::Right(left, right) => TermKind::Right(left, right),
            TermNode::Case(left, right) => TermKind::Case(left, right),
            TermNode::Curry(inner) => TermKind::Curry(inner),
            TermNode::Eval(domain, codomain) => TermKind::Eval(domain, codomain),
        }
    }

    fn ensure_object(signature: &Signature, object: &Object) -> Result<(), TermError> {
        let ctx = signature.context_id();
        object
            .ensure_context(ctx)
            .map_err(TermError::from_object_error)
    }

    fn ensure_term(signature: &Signature, term: &Term) -> Result<(), TermError> {
        let expected = signature.context_id();
        if term.0.signature == expected {
            Ok(())
        } else {
            Err(TermError::SignatureMismatch {
                expected,
                actual: term.0.signature,
            })
        }
    }

    /// `generator[q]`
    pub fn generator(signature: &Signature, id: GeneratorId) -> Result<Self, TermError> {
        signature
            .generator(id)
            .map_err(|_| TermError::InvalidGeneratorId(id))?;
        Ok(Self::new(signature.context_id(), TermNode::Generator(id)))
    }

    /// `id[A]`
    pub fn id(signature: &Signature, object: &Object) -> Result<Self, TermError> {
        Self::ensure_object(signature, object)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Id(object.clone()),
        ))
    }

    /// `t >>> u` (may be categorically ill typed).
    pub fn compose(signature: &Signature, left: &Term, right: &Term) -> Result<Self, TermError> {
        Self::ensure_term(signature, left)?;
        Self::ensure_term(signature, right)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Compose(left.clone(), right.clone()),
        ))
    }

    /// `discard[A]`
    pub fn discard(signature: &Signature, object: &Object) -> Result<Self, TermError> {
        Self::ensure_object(signature, object)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Discard(object.clone()),
        ))
    }

    /// `absurd[A]`
    pub fn absurd(signature: &Signature, object: &Object) -> Result<Self, TermError> {
        Self::ensure_object(signature, object)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Absurd(object.clone()),
        ))
    }

    /// `first[A, B]`
    pub fn first(signature: &Signature, left: &Object, right: &Object) -> Result<Self, TermError> {
        Self::ensure_object(signature, left)?;
        Self::ensure_object(signature, right)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::First(left.clone(), right.clone()),
        ))
    }

    /// `second[A, B]`
    pub fn second(signature: &Signature, left: &Object, right: &Object) -> Result<Self, TermError> {
        Self::ensure_object(signature, left)?;
        Self::ensure_object(signature, right)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Second(left.clone(), right.clone()),
        ))
    }

    /// `pair(t, u)` (sources may mismatch for diagnostics).
    pub fn pair(signature: &Signature, left: &Term, right: &Term) -> Result<Self, TermError> {
        Self::ensure_term(signature, left)?;
        Self::ensure_term(signature, right)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Pair(left.clone(), right.clone()),
        ))
    }

    /// `left[A, B]`
    pub fn left(signature: &Signature, left: &Object, right: &Object) -> Result<Self, TermError> {
        Self::ensure_object(signature, left)?;
        Self::ensure_object(signature, right)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Left(left.clone(), right.clone()),
        ))
    }

    /// `right[A, B]`
    pub fn right(signature: &Signature, left: &Object, right: &Object) -> Result<Self, TermError> {
        Self::ensure_object(signature, left)?;
        Self::ensure_object(signature, right)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Right(left.clone(), right.clone()),
        ))
    }

    /// `case(t, u)` (targets may mismatch for diagnostics).
    pub fn case(signature: &Signature, left: &Term, right: &Term) -> Result<Self, TermError> {
        Self::ensure_term(signature, left)?;
        Self::ensure_term(signature, right)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Case(left.clone(), right.clone()),
        ))
    }

    /// `curry(t)` (source may fail to be a product at check time).
    pub fn curry(signature: &Signature, inner: &Term) -> Result<Self, TermError> {
        Self::ensure_term(signature, inner)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Curry(inner.clone()),
        ))
    }

    /// `eval[A, B]`
    pub fn eval(
        signature: &Signature,
        domain: &Object,
        codomain: &Object,
    ) -> Result<Self, TermError> {
        Self::ensure_object(signature, domain)?;
        Self::ensure_object(signature, codomain)?;
        Ok(Self::new(
            signature.context_id(),
            TermNode::Eval(domain.clone(), codomain.clone()),
        ))
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref() == other.0.as_ref()
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Term")
            .field("signature", &self.0.signature)
            .field("node", &self.0.node)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::object_expr::ObjectExpr;
    use crate::signature::SignatureBuilder;

    fn number_signature() -> Signature {
        let mut builder = SignatureBuilder::new();
        builder.add_base("Number").expect("base");
        builder
            .add_generator("two", ObjectExpr::unit(), ObjectExpr::base(name("Number")))
            .expect("two");
        builder
            .add_generator(
                "add",
                ObjectExpr::product(
                    ObjectExpr::base(name("Number")),
                    ObjectExpr::base(name("Number")),
                ),
                ObjectExpr::base(name("Number")),
            )
            .expect("add");
        builder.build().expect("signature")
    }

    fn name(text: &str) -> crate::name::Name {
        crate::name::Name::new(text).expect("valid")
    }

    #[test]
    fn constructs_ill_typed_composition() {
        let signature = number_signature();
        let two =
            Term::generator(&signature, signature.generator_id("two").expect("two")).expect("term");
        let add =
            Term::generator(&signature, signature.generator_id("add").expect("add")).expect("term");
        let composed = Term::compose(&signature, &two, &add).expect("structurally valid");
        assert!(matches!(composed.kind(), TermKind::Compose(_, _)));
    }

    #[test]
    fn rejects_cross_signature_objects() {
        let left = number_signature();
        let right = number_signature();
        let err = Term::id(&left, &right.unit()).expect_err("mismatch");
        assert!(matches!(err, TermError::SignatureMismatch { .. }));
    }

    #[test]
    fn rejects_invalid_generator_id() {
        let signature = number_signature();
        let err = Term::generator(&signature, GeneratorId::new(99)).expect_err("bad id");
        assert!(matches!(err, TermError::InvalidGeneratorId(_)));
    }
}
