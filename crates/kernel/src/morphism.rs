//! Trusted checked morphisms.
//!
//! Crate-private constructors each enforce the typing rule for their node and
//! **derive** source/target objects from `&Signature` and operands. They do not
//! accept caller-supplied derived objects (products, exponentials, `Unit`, …).
//!
//! [`crate::check`] translates failures into user-facing [`crate::CheckError`]s;
//! constructor invariant failures surface as [`KernelFault`].

use std::fmt;
use std::sync::Arc;

use crate::error::{KernelFault, ObjectError};
use crate::id::GeneratorId;
use crate::object::{Object, ObjectKind};
use crate::signature::Signature;

/// Trusted typed morphism `source ⟶ target` under one signature context.
#[derive(Clone, Eq)]
pub struct Morphism(Arc<MorphismData>);

#[derive(Clone, PartialEq, Eq, Debug)]
struct MorphismData {
    signature: crate::id::SignatureContextId,
    source: Object,
    target: Object,
    node: MorphismNode,
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum MorphismNode {
    Generator(GeneratorId),
    Id,
    Compose(Morphism, Morphism),
    Discard,
    Absurd,
    First,
    Second,
    Pair(Morphism, Morphism),
    Left,
    Right,
    Case(Morphism, Morphism),
    Curry(Morphism),
    Eval,
}

/// Borrowed view of a checked morphism node.
#[derive(Clone, Copy, Debug)]
pub enum MorphismKind<'a> {
    Generator(GeneratorId),
    Id,
    Compose(&'a Morphism, &'a Morphism),
    Discard,
    Absurd,
    First,
    Second,
    Pair(&'a Morphism, &'a Morphism),
    Left,
    Right,
    Case(&'a Morphism, &'a Morphism),
    Curry(&'a Morphism),
    Eval,
}

impl Morphism {
    fn new(
        signature: &Signature,
        source: Object,
        target: Object,
        node: MorphismNode,
    ) -> Result<Self, KernelFault> {
        let ctx = signature.context_id();
        if source.signature_context() != ctx || target.signature_context() != ctx {
            return Err(KernelFault::new(
                "morphism object signature does not match morphism context",
            ));
        }
        Ok(Self(Arc::new(MorphismData {
            signature: ctx,
            source,
            target,
            node,
        })))
    }

    fn object_fault(err: ObjectError) -> KernelFault {
        match err {
            ObjectError::SignatureMismatch { .. } => {
                KernelFault::new("morphism operand signature mismatch")
            }
        }
    }

    /// Exact signature context.
    pub fn signature_context(&self) -> crate::id::SignatureContextId {
        self.0.signature
    }

    /// Source object.
    pub fn source(&self) -> &Object {
        &self.0.source
    }

    /// Target object.
    pub fn target(&self) -> &Object {
        &self.0.target
    }

    /// Exhaustive constructor view.
    pub fn kind(&self) -> MorphismKind<'_> {
        match &self.0.node {
            MorphismNode::Generator(id) => MorphismKind::Generator(*id),
            MorphismNode::Id => MorphismKind::Id,
            MorphismNode::Compose(left, right) => MorphismKind::Compose(left, right),
            MorphismNode::Discard => MorphismKind::Discard,
            MorphismNode::Absurd => MorphismKind::Absurd,
            MorphismNode::First => MorphismKind::First,
            MorphismNode::Second => MorphismKind::Second,
            MorphismNode::Pair(left, right) => MorphismKind::Pair(left, right),
            MorphismNode::Left => MorphismKind::Left,
            MorphismNode::Right => MorphismKind::Right,
            MorphismNode::Case(left, right) => MorphismKind::Case(left, right),
            MorphismNode::Curry(inner) => MorphismKind::Curry(inner),
            MorphismNode::Eval => MorphismKind::Eval,
        }
    }

    /// `generator[q] : A ⟶ B` from the signature declaration.
    pub(crate) fn generator(signature: &Signature, id: GeneratorId) -> Result<Self, KernelFault> {
        let decl = signature
            .generator(id)
            .map_err(|_| KernelFault::new("invalid generator id in trusted constructor"))?;
        Self::new(
            signature,
            decl.source().clone(),
            decl.target().clone(),
            MorphismNode::Generator(id),
        )
    }

    /// `id[A] : A ⟶ A`.
    pub(crate) fn id(signature: &Signature, object: &Object) -> Result<Self, KernelFault> {
        object
            .ensure_context(signature.context_id())
            .map_err(Self::object_fault)?;
        Self::new(signature, object.clone(), object.clone(), MorphismNode::Id)
    }

    /// `left >>> right` when middle objects match.
    pub(crate) fn compose(left: Self, right: Self) -> Result<Self, KernelFault> {
        if left.0.signature != right.0.signature {
            return Err(KernelFault::new("compose signature mismatch"));
        }
        if left.0.target != right.0.source {
            return Err(KernelFault::new("compose middle object mismatch"));
        }
        // Reconstruct via context id only; both morphisms already carry objects.
        Ok(Self(Arc::new(MorphismData {
            signature: left.0.signature,
            source: left.0.source.clone(),
            target: right.0.target.clone(),
            node: MorphismNode::Compose(left, right),
        })))
    }

    /// `discard[A] : A ⟶ Unit`.
    pub(crate) fn discard(signature: &Signature, source: &Object) -> Result<Self, KernelFault> {
        source
            .ensure_context(signature.context_id())
            .map_err(Self::object_fault)?;
        Self::new(
            signature,
            source.clone(),
            signature.unit(),
            MorphismNode::Discard,
        )
    }

    /// `absurd[A] : Never ⟶ A`.
    pub(crate) fn absurd(signature: &Signature, target: &Object) -> Result<Self, KernelFault> {
        target
            .ensure_context(signature.context_id())
            .map_err(Self::object_fault)?;
        Self::new(
            signature,
            signature.never(),
            target.clone(),
            MorphismNode::Absurd,
        )
    }

    /// `first[A, B] : A × B ⟶ A`.
    pub(crate) fn first(
        signature: &Signature,
        left: &Object,
        right: &Object,
    ) -> Result<Self, KernelFault> {
        let product = signature.product(left, right).map_err(Self::object_fault)?;
        Self::new(signature, product, left.clone(), MorphismNode::First)
    }

    /// `second[A, B] : A × B ⟶ B`.
    pub(crate) fn second(
        signature: &Signature,
        left: &Object,
        right: &Object,
    ) -> Result<Self, KernelFault> {
        let product = signature.product(left, right).map_err(Self::object_fault)?;
        Self::new(signature, product, right.clone(), MorphismNode::Second)
    }

    /// `pair(f, g) : X ⟶ A × B` when sources match.
    pub(crate) fn pair(
        signature: &Signature,
        left: Self,
        right: Self,
    ) -> Result<Self, KernelFault> {
        if left.0.signature != signature.context_id() || right.0.signature != signature.context_id()
        {
            return Err(KernelFault::new("pair signature mismatch"));
        }
        if left.0.source != right.0.source {
            return Err(KernelFault::new("pair source mismatch"));
        }
        let product = signature
            .product(&left.0.target, &right.0.target)
            .map_err(Self::object_fault)?;
        Self::new(
            signature,
            left.0.source.clone(),
            product,
            MorphismNode::Pair(left, right),
        )
    }

    /// `left[A, B] : A ⟶ A + B`.
    pub(crate) fn left(
        signature: &Signature,
        left: &Object,
        right: &Object,
    ) -> Result<Self, KernelFault> {
        let coproduct = signature
            .coproduct(left, right)
            .map_err(Self::object_fault)?;
        Self::new(signature, left.clone(), coproduct, MorphismNode::Left)
    }

    /// `right[A, B] : B ⟶ A + B`.
    pub(crate) fn right(
        signature: &Signature,
        left: &Object,
        right: &Object,
    ) -> Result<Self, KernelFault> {
        let coproduct = signature
            .coproduct(left, right)
            .map_err(Self::object_fault)?;
        Self::new(signature, right.clone(), coproduct, MorphismNode::Right)
    }

    /// `case(f, g) : A + B ⟶ X` when targets match.
    pub(crate) fn case(
        signature: &Signature,
        left: Self,
        right: Self,
    ) -> Result<Self, KernelFault> {
        if left.0.signature != signature.context_id() || right.0.signature != signature.context_id()
        {
            return Err(KernelFault::new("case signature mismatch"));
        }
        if left.0.target != right.0.target {
            return Err(KernelFault::new("case target mismatch"));
        }
        let coproduct = signature
            .coproduct(&left.0.source, &right.0.source)
            .map_err(Self::object_fault)?;
        Self::new(
            signature,
            coproduct,
            left.0.target.clone(),
            MorphismNode::Case(left, right),
        )
    }

    /// `curry(f) : X ⟶ A ⇒ B` when `f : X × A ⟶ B`.
    pub(crate) fn curry(signature: &Signature, inner: Self) -> Result<Self, KernelFault> {
        if inner.0.signature != signature.context_id() {
            return Err(KernelFault::new("curry signature mismatch"));
        }
        let ObjectKind::Product(x, a) = inner.0.source.kind() else {
            return Err(KernelFault::new("curry source is not a product"));
        };
        let x = x.clone();
        let a = a.clone();
        let exponential = signature
            .exponential(&a, &inner.0.target)
            .map_err(Self::object_fault)?;
        Self::new(signature, x, exponential, MorphismNode::Curry(inner))
    }

    /// `eval[A, B] : (A ⇒ B) × A ⟶ B`.
    pub(crate) fn eval(
        signature: &Signature,
        domain: &Object,
        codomain: &Object,
    ) -> Result<Self, KernelFault> {
        let exponential = signature
            .exponential(domain, codomain)
            .map_err(Self::object_fault)?;
        let source = signature
            .product(&exponential, domain)
            .map_err(Self::object_fault)?;
        Self::new(signature, source, codomain.clone(), MorphismNode::Eval)
    }
}

impl PartialEq for Morphism {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref() == other.0.as_ref()
    }
}

impl fmt::Debug for Morphism {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Morphism")
            .field("signature", &self.0.signature)
            .field("source", &self.0.source)
            .field("target", &self.0.target)
            .field("node", &self.0.node)
            .finish()
    }
}
