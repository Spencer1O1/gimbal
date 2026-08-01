//! Signature builder and immutable resolved signatures.
//!
//! Construction validates names, assigns deterministic typed IDs, resolves
//! [`ObjectExpr`]s, computes `SHA-256` of the canonical encoding, and mints a
//! fresh [`SignatureContextId`].

use std::collections::HashMap;
use std::sync::Arc;

use sha2::{Digest, Sha256};

use crate::error::{ObjectError, SignatureError};
use crate::id::{BaseId, GeneratorId, SignatureContextId, SignatureFingerprint};
use crate::name::Name;
use crate::object::{Object, ObjectNode};
use crate::object_expr::ObjectExpr;

/// Mutable builder for a [`Signature`].
#[derive(Debug, Default)]
pub struct SignatureBuilder {
    bases: Vec<Name>,
    base_ids: HashMap<Name, BaseId>,
    generators: Vec<PendingGenerator>,
    generator_ids: HashMap<Name, GeneratorId>,
}

#[derive(Debug)]
struct PendingGenerator {
    name: Name,
    id: GeneratorId,
    source: ObjectExpr,
    target: ObjectExpr,
}

/// Fixed ASCII domain separator for the canonical signature encoding.
const ENCODING_MAGIC: &[u8] = b"GIMBALSIG";

/// Version of the canonical signature encoding byte format.
const ENCODING_VERSION: u32 = 1;

/// Immutable resolved signature.
#[derive(Clone, Debug)]
pub struct Signature {
    inner: Arc<SignatureData>,
}

#[derive(Debug)]
struct SignatureData {
    context: SignatureContextId,
    fingerprint: SignatureFingerprint,
    bases: Box<[Name]>,
    generators: Box<[GeneratorDecl]>,
}

/// One resolved generating morphism declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratorDecl {
    name: Name,
    id: GeneratorId,
    source: Object,
    target: Object,
}

impl GeneratorDecl {
    /// Generator name as declared.
    pub fn name(&self) -> &Name {
        &self.name
    }

    /// Dense generator id.
    pub fn id(&self) -> GeneratorId {
        self.id
    }

    /// Declared source object.
    pub fn source(&self) -> &Object {
        &self.source
    }

    /// Declared target object.
    pub fn target(&self) -> &Object {
        &self.target
    }
}

impl SignatureBuilder {
    /// Empty builder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Declare a base object. IDs are assigned in declaration order.
    ///
    /// Base names are a separate namespace from generator names.
    pub fn add_base(&mut self, name: impl AsRef<str>) -> Result<BaseId, SignatureError> {
        let name = Name::new(name)?;
        if self.base_ids.contains_key(&name) {
            return Err(SignatureError::DuplicateBase(name));
        }
        let id =
            BaseId::new(u32::try_from(self.bases.len()).map_err(|_| SignatureError::TooManyBases)?);
        self.bases.push(name.clone());
        self.base_ids.insert(name, id);
        Ok(id)
    }

    /// Declare a generating morphism with unresolved source and target objects.
    ///
    /// Generator names are a separate namespace from base names. Source and target
    /// expressions may only refer to bases already declared on this builder.
    pub fn add_generator(
        &mut self,
        name: impl AsRef<str>,
        source: ObjectExpr,
        target: ObjectExpr,
    ) -> Result<GeneratorId, SignatureError> {
        let name = Name::new(name)?;
        if self.generator_ids.contains_key(&name) {
            return Err(SignatureError::DuplicateGenerator(name));
        }

        // Fail fast on undeclared bases while the generator name is in scope.
        validate_expr_bases(&source, &self.base_ids, &name)?;
        validate_expr_bases(&target, &self.base_ids, &name)?;

        let id = GeneratorId::new(
            u32::try_from(self.generators.len()).map_err(|_| SignatureError::TooManyGenerators)?,
        );
        self.generators.push(PendingGenerator {
            name: name.clone(),
            id,
            source,
            target,
        });
        self.generator_ids.insert(name, id);
        Ok(id)
    }

    /// Freeze the builder into an immutable signature.
    pub fn build(self) -> Result<Signature, SignatureError> {
        let context = SignatureContextId::fresh();
        let encoding = encode_canonical_signature(&self.bases, &self.generators, &self.base_ids)?;
        let digest = Sha256::digest(&encoding);
        let fingerprint = SignatureFingerprint::from_sha256(digest.into());

        let mut resolved = Vec::with_capacity(self.generators.len());
        for pending in self.generators {
            let source = resolve_expr(&pending.source, context, &self.base_ids, &pending.name)?;
            let target = resolve_expr(&pending.target, context, &self.base_ids, &pending.name)?;
            resolved.push(GeneratorDecl {
                name: pending.name,
                id: pending.id,
                source,
                target,
            });
        }

        Ok(Signature {
            inner: Arc::new(SignatureData {
                context,
                fingerprint,
                bases: self.bases.into_boxed_slice(),
                generators: resolved.into_boxed_slice(),
            }),
        })
    }
}

impl Signature {
    /// Exact process-local context identity.
    pub fn context_id(&self) -> SignatureContextId {
        self.inner.context
    }

    /// Canonical content fingerprint.
    pub fn fingerprint(&self) -> &SignatureFingerprint {
        &self.inner.fingerprint
    }

    /// Number of declared bases.
    pub fn base_count(&self) -> usize {
        self.inner.bases.len()
    }

    /// Number of declared generators.
    pub fn generator_count(&self) -> usize {
        self.inner.generators.len()
    }

    /// Name of a declared base.
    pub fn base_name(&self, id: BaseId) -> Result<&Name, SignatureError> {
        self.inner
            .bases
            .get(id.as_u32() as usize)
            .ok_or(SignatureError::InvalidBaseId(id))
    }

    /// Look up a base id by name.
    pub fn base_id(&self, name: &str) -> Option<BaseId> {
        self.inner
            .bases
            .iter()
            .position(|n| n.as_str() == name)
            .and_then(|index| u32::try_from(index).ok().map(BaseId::new))
    }

    /// Resolved generator declaration.
    pub fn generator(&self, id: GeneratorId) -> Result<&GeneratorDecl, SignatureError> {
        self.inner
            .generators
            .get(id.as_u32() as usize)
            .ok_or(SignatureError::InvalidGeneratorId(id))
    }

    /// Look up a generator id by name.
    pub fn generator_id(&self, name: &str) -> Option<GeneratorId> {
        self.inner
            .generators
            .iter()
            .find(|decl| decl.name.as_str() == name)
            .map(GeneratorDecl::id)
    }

    /// Resolved base object for `id`.
    pub fn base(&self, id: BaseId) -> Result<Object, SignatureError> {
        let _ = self.base_name(id)?;
        Ok(Object::new(self.inner.context, ObjectNode::Base(id)))
    }

    /// Terminal object in this signature context.
    pub fn unit(&self) -> Object {
        Object::new(self.inner.context, ObjectNode::Unit)
    }

    /// Initial object in this signature context.
    pub fn never(&self) -> Object {
        Object::new(self.inner.context, ObjectNode::Never)
    }

    /// Product of two objects from this signature.
    pub fn product(&self, left: &Object, right: &Object) -> Result<Object, ObjectError> {
        left.ensure_context(self.inner.context)?;
        right.ensure_context(self.inner.context)?;
        Ok(Object::new(
            self.inner.context,
            ObjectNode::Product(left.clone(), right.clone()),
        ))
    }

    /// Coproduct of two objects from this signature.
    pub fn coproduct(&self, left: &Object, right: &Object) -> Result<Object, ObjectError> {
        left.ensure_context(self.inner.context)?;
        right.ensure_context(self.inner.context)?;
        Ok(Object::new(
            self.inner.context,
            ObjectNode::Coproduct(left.clone(), right.clone()),
        ))
    }

    /// Exponential `domain ⇒ codomain` in this signature.
    pub fn exponential(&self, domain: &Object, codomain: &Object) -> Result<Object, ObjectError> {
        domain.ensure_context(self.inner.context)?;
        codomain.ensure_context(self.inner.context)?;
        Ok(Object::new(
            self.inner.context,
            ObjectNode::Exponential(domain.clone(), codomain.clone()),
        ))
    }
}

fn validate_expr_bases(
    expr: &ObjectExpr,
    bases: &HashMap<Name, BaseId>,
    generator: &Name,
) -> Result<(), SignatureError> {
    match expr {
        ObjectExpr::Base(name) => {
            if bases.contains_key(name) {
                Ok(())
            } else {
                Err(SignatureError::UndeclaredBase {
                    generator: generator.clone(),
                    base: name.clone(),
                })
            }
        }
        ObjectExpr::Unit | ObjectExpr::Never => Ok(()),
        ObjectExpr::Product(left, right)
        | ObjectExpr::Coproduct(left, right)
        | ObjectExpr::Exponential(left, right) => {
            validate_expr_bases(left, bases, generator)?;
            validate_expr_bases(right, bases, generator)
        }
    }
}

fn resolve_expr(
    expr: &ObjectExpr,
    context: SignatureContextId,
    bases: &HashMap<Name, BaseId>,
    generator: &Name,
) -> Result<Object, SignatureError> {
    let node = match expr {
        ObjectExpr::Base(name) => {
            let id = bases
                .get(name)
                .copied()
                .ok_or_else(|| SignatureError::UndeclaredBase {
                    generator: generator.clone(),
                    base: name.clone(),
                })?;
            ObjectNode::Base(id)
        }
        ObjectExpr::Unit => ObjectNode::Unit,
        ObjectExpr::Never => ObjectNode::Never,
        ObjectExpr::Product(left, right) => ObjectNode::Product(
            resolve_expr(left, context, bases, generator)?,
            resolve_expr(right, context, bases, generator)?,
        ),
        ObjectExpr::Coproduct(left, right) => ObjectNode::Coproduct(
            resolve_expr(left, context, bases, generator)?,
            resolve_expr(right, context, bases, generator)?,
        ),
        ObjectExpr::Exponential(domain, codomain) => ObjectNode::Exponential(
            resolve_expr(domain, context, bases, generator)?,
            resolve_expr(codomain, context, bases, generator)?,
        ),
    };
    Ok(Object::new(context, node))
}

/// Canonical signature encoding. Fingerprints are `SHA-256` of this byte string.
///
/// Encoding rules (big-endian lengths, declaration order):
/// - ASCII magic `GIMBALSIG`
/// - `u32` BE format version (`ENCODING_VERSION`)
/// - `u32` base count, then each base name as `u32` byte length + UTF-8
/// - `u32` generator count, then each generator:
///   - name as `u32` length + UTF-8
///   - source object encoding
///   - target object encoding
///
/// Object tags: `0` Unit, `1` Never, `2` Base + `u32` id, `3` Product,
/// `4` Coproduct, `5` Exponential; binary constructors are immediately
/// followed by their children.
///
/// Base/generator counts are bounded by the builder (`u32::MAX`).
fn encode_canonical_signature(
    bases: &[Name],
    generators: &[PendingGenerator],
    base_ids: &HashMap<Name, BaseId>,
) -> Result<Vec<u8>, SignatureError> {
    let mut out = Vec::new();
    out.extend_from_slice(ENCODING_MAGIC);
    write_u32(&mut out, ENCODING_VERSION);
    write_u32(
        &mut out,
        u32::try_from(bases.len()).map_err(|_| SignatureError::TooManyBases)?,
    );
    for name in bases {
        write_name(&mut out, name);
    }
    write_u32(
        &mut out,
        u32::try_from(generators.len()).map_err(|_| SignatureError::TooManyGenerators)?,
    );
    for generator in generators {
        write_name(&mut out, &generator.name);
        encode_object_expr(&mut out, &generator.source, base_ids, &generator.name)?;
        encode_object_expr(&mut out, &generator.target, base_ids, &generator.name)?;
    }
    Ok(out)
}

fn encode_object_expr(
    out: &mut Vec<u8>,
    expr: &ObjectExpr,
    base_ids: &HashMap<Name, BaseId>,
    generator: &Name,
) -> Result<(), SignatureError> {
    match expr {
        ObjectExpr::Unit => out.push(0),
        ObjectExpr::Never => out.push(1),
        ObjectExpr::Base(name) => {
            out.push(2);
            let id = base_ids
                .get(name)
                .ok_or_else(|| SignatureError::UndeclaredBase {
                    generator: generator.clone(),
                    base: name.clone(),
                })?;
            write_u32(out, id.as_u32());
        }
        ObjectExpr::Product(left, right) => {
            out.push(3);
            encode_object_expr(out, left, base_ids, generator)?;
            encode_object_expr(out, right, base_ids, generator)?;
        }
        ObjectExpr::Coproduct(left, right) => {
            out.push(4);
            encode_object_expr(out, left, base_ids, generator)?;
            encode_object_expr(out, right, base_ids, generator)?;
        }
        ObjectExpr::Exponential(domain, codomain) => {
            out.push(5);
            encode_object_expr(out, domain, base_ids, generator)?;
            encode_object_expr(out, codomain, base_ids, generator)?;
        }
    }
    Ok(())
}

fn write_name(out: &mut Vec<u8>, name: &Name) {
    let bytes = name.as_str().as_bytes();
    write_u32(out, name.len_u32());
    out.extend_from_slice(bytes);
}

fn write_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_be_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::object::ObjectKind;

    fn number_signature() -> Signature {
        let mut builder = SignatureBuilder::new();
        builder.add_base("Number").expect("base");
        builder
            .add_generator("two", ObjectExpr::unit(), ObjectExpr::base(name("Number")))
            .expect("two");
        builder
            .add_generator(
                "three",
                ObjectExpr::unit(),
                ObjectExpr::base(name("Number")),
            )
            .expect("three");
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

    fn name(text: &str) -> Name {
        Name::new(text).expect("valid name")
    }

    #[test]
    fn assigns_deterministic_ids_in_declaration_order() {
        let signature = number_signature();
        assert_eq!(signature.base_id("Number"), Some(BaseId::new(0)));
        assert_eq!(signature.generator_id("two"), Some(GeneratorId::new(0)));
        assert_eq!(signature.generator_id("three"), Some(GeneratorId::new(1)));
        assert_eq!(signature.generator_id("add"), Some(GeneratorId::new(2)));
    }

    #[test]
    fn identical_contents_share_fingerprint_not_context() {
        let left = number_signature();
        let right = number_signature();
        assert_eq!(left.fingerprint(), right.fingerprint());
        assert_ne!(left.context_id(), right.context_id());
        assert_eq!(left.fingerprint().as_bytes().len(), 32);
    }

    #[test]
    fn rejects_duplicate_base() {
        let mut builder = SignatureBuilder::new();
        builder.add_base("Number").expect("first");
        let err = builder.add_base("Number").expect_err("duplicate");
        assert!(matches!(err, SignatureError::DuplicateBase(_)));
    }

    #[test]
    fn rejects_duplicate_generator() {
        let mut builder = SignatureBuilder::new();
        builder.add_base("Number").expect("base");
        builder
            .add_generator("two", ObjectExpr::unit(), ObjectExpr::base(name("Number")))
            .expect("first");
        let err = builder
            .add_generator("two", ObjectExpr::unit(), ObjectExpr::base(name("Number")))
            .expect_err("duplicate");
        assert!(matches!(err, SignatureError::DuplicateGenerator(_)));
    }

    #[test]
    fn rejects_undeclared_base() {
        let mut builder = SignatureBuilder::new();
        let err = builder
            .add_generator("two", ObjectExpr::unit(), ObjectExpr::base(name("Number")))
            .expect_err("undeclared");
        match err {
            SignatureError::UndeclaredBase { generator, base } => {
                assert_eq!(generator.as_str(), "two");
                assert_eq!(base.as_str(), "Number");
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn resolves_generator_objects() {
        let signature = number_signature();
        let add = signature
            .generator(signature.generator_id("add").expect("add"))
            .expect("decl");
        assert!(matches!(add.source().kind(), ObjectKind::Product(_, _)));
        assert!(matches!(add.target().kind(), ObjectKind::Base(id) if id == BaseId::new(0)));
        assert_eq!(add.source().signature_context(), signature.context_id());
    }

    #[test]
    fn rejects_cross_signature_products() {
        let left = number_signature();
        let right = number_signature();
        let err = left
            .product(&left.unit(), &right.unit())
            .expect_err("mismatch");
        assert!(matches!(err, ObjectError::SignatureMismatch { .. }));
    }

    #[test]
    fn fingerprint_follows_declaration_order_not_names_alone() {
        let mut ab = SignatureBuilder::new();
        ab.add_base("A").expect("A");
        ab.add_base("B").expect("B");
        let sig_ab = ab.build().expect("AB");

        let mut ba = SignatureBuilder::new();
        ba.add_base("B").expect("B");
        ba.add_base("A").expect("A");
        let sig_ba = ba.build().expect("BA");

        assert_ne!(sig_ab.fingerprint(), sig_ba.fingerprint());
    }

    #[test]
    fn canonical_encoding_starts_with_magic_and_version() {
        let encoding = encode_canonical_signature(&[], &[], &HashMap::new()).expect("empty");
        assert!(encoding.starts_with(ENCODING_MAGIC));
        assert_eq!(
            &encoding[ENCODING_MAGIC.len()..ENCODING_MAGIC.len() + 4],
            &1u32.to_be_bytes()
        );
    }

    #[test]
    fn allows_same_spelling_in_base_and_generator_namespaces() {
        let mut builder = SignatureBuilder::new();
        builder.add_base("X").expect("base");
        builder
            .add_generator("X", ObjectExpr::unit(), ObjectExpr::base(name("X")))
            .expect("generator");
        let signature = builder.build().expect("signature");
        assert_eq!(signature.base_id("X"), Some(BaseId::new(0)));
        assert_eq!(signature.generator_id("X"), Some(GeneratorId::new(0)));
    }
}
