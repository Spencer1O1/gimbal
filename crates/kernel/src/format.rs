//! Deterministic **human** display of Phase 0 kernel IR (diagnostics, tests, snapshots).
//!
//! This is not source syntax, not a wire format, and not round-trippable: a declared
//! base named `Unit` prints the same as the terminal object. Do not parse these
//! strings back into kernel values; the IR remains the Rust trees (and later Lean).
//!
//! Notation follows the Semantic Core (locked for Phase 0 display):
//! - objects: `Unit`, `Never`, `A × B`, `A + B`, `A ⇒ B`, bases by declared name
//! - arrows: `A ⟶ B` (morphism) vs `A ⇒ B` (exponential object)
//! - composition: `t >>> u`, always parenthesized as `(t >>> u)`
//! - binary object constructors are always parenthesized so association is explicit
//!
//! All entry points take a [`Signature`] and reject cross-context values.

use crate::error::FormatError;
use crate::id::{BaseId, GeneratorId};
use crate::morphism::{Morphism, MorphismKind};
use crate::object::{Object, ObjectKind};
use crate::signature::Signature;
use crate::term::{Term, TermKind};

/// Format a resolved object under `signature`.
pub fn format_object(signature: &Signature, object: &Object) -> Result<String, FormatError> {
    ensure_object(signature, object)?;
    fmt_object(signature, object)
}

/// Format an explicit term under `signature`.
pub fn format_term(signature: &Signature, term: &Term) -> Result<String, FormatError> {
    ensure_term(signature, term)?;
    fmt_term(signature, term)
}

/// Format a checked morphism under `signature` (also used for simplified morphisms).
pub fn format_morphism(signature: &Signature, morphism: &Morphism) -> Result<String, FormatError> {
    ensure_morphism(signature, morphism)?;
    fmt_morphism(signature, morphism)
}

/// Format `source ⟶ target`.
pub fn format_arrow(
    signature: &Signature,
    source: &Object,
    target: &Object,
) -> Result<String, FormatError> {
    ensure_object(signature, source)?;
    ensure_object(signature, target)?;
    Ok(format!(
        "{} ⟶ {}",
        fmt_object(signature, source)?,
        fmt_object(signature, target)?
    ))
}

/// Format `morphism : source ⟶ target`.
pub fn format_typed_morphism(
    signature: &Signature,
    morphism: &Morphism,
) -> Result<String, FormatError> {
    ensure_morphism(signature, morphism)?;
    Ok(format!(
        "{} : {}",
        fmt_morphism(signature, morphism)?,
        format_arrow(signature, morphism.source(), morphism.target())?
    ))
}

fn ensure_object(signature: &Signature, object: &Object) -> Result<(), FormatError> {
    let expected = signature.context_id();
    if object.signature_context() == expected {
        Ok(())
    } else {
        Err(FormatError::SignatureMismatch {
            expected,
            actual: object.signature_context(),
        })
    }
}

fn ensure_term(signature: &Signature, term: &Term) -> Result<(), FormatError> {
    let expected = signature.context_id();
    if term.signature_context() == expected {
        Ok(())
    } else {
        Err(FormatError::SignatureMismatch {
            expected,
            actual: term.signature_context(),
        })
    }
}

fn ensure_morphism(signature: &Signature, morphism: &Morphism) -> Result<(), FormatError> {
    let expected = signature.context_id();
    if morphism.signature_context() == expected {
        Ok(())
    } else {
        Err(FormatError::SignatureMismatch {
            expected,
            actual: morphism.signature_context(),
        })
    }
}

fn base_name(signature: &Signature, id: BaseId) -> Result<&str, FormatError> {
    signature
        .base_name(id)
        .map(|n| n.as_str())
        .map_err(|_| FormatError::InvalidBaseId(id))
}

fn generator_name(signature: &Signature, id: GeneratorId) -> Result<&str, FormatError> {
    signature
        .generator(id)
        .map(|d| d.name().as_str())
        .map_err(|_| FormatError::InvalidGeneratorId(id))
}

fn fmt_object(signature: &Signature, object: &Object) -> Result<String, FormatError> {
    match object.kind() {
        ObjectKind::Base(id) => Ok(base_name(signature, id)?.to_owned()),
        ObjectKind::Unit => Ok("Unit".to_owned()),
        ObjectKind::Never => Ok("Never".to_owned()),
        ObjectKind::Product(left, right) => Ok(format!(
            "({} × {})",
            fmt_object(signature, left)?,
            fmt_object(signature, right)?
        )),
        ObjectKind::Coproduct(left, right) => Ok(format!(
            "({} + {})",
            fmt_object(signature, left)?,
            fmt_object(signature, right)?
        )),
        ObjectKind::Exponential(domain, codomain) => Ok(format!(
            "({} ⇒ {})",
            fmt_object(signature, domain)?,
            fmt_object(signature, codomain)?
        )),
    }
}

fn fmt_term(signature: &Signature, term: &Term) -> Result<String, FormatError> {
    match term.kind() {
        TermKind::Generator(id) => Ok(generator_name(signature, id)?.to_owned()),
        TermKind::Id(object) => Ok(format!("id[{}]", fmt_object(signature, object)?)),
        TermKind::Compose(left, right) => Ok(format!(
            "({} >>> {})",
            fmt_term(signature, left)?,
            fmt_term(signature, right)?
        )),
        TermKind::Discard(object) => Ok(format!("discard[{}]", fmt_object(signature, object)?)),
        TermKind::Absurd(object) => Ok(format!("absurd[{}]", fmt_object(signature, object)?)),
        TermKind::First(left, right) => Ok(format!(
            "first[{}, {}]",
            fmt_object(signature, left)?,
            fmt_object(signature, right)?
        )),
        TermKind::Second(left, right) => Ok(format!(
            "second[{}, {}]",
            fmt_object(signature, left)?,
            fmt_object(signature, right)?
        )),
        TermKind::Pair(left, right) => Ok(format!(
            "pair({}, {})",
            fmt_term(signature, left)?,
            fmt_term(signature, right)?
        )),
        TermKind::Left(left, right) => Ok(format!(
            "left[{}, {}]",
            fmt_object(signature, left)?,
            fmt_object(signature, right)?
        )),
        TermKind::Right(left, right) => Ok(format!(
            "right[{}, {}]",
            fmt_object(signature, left)?,
            fmt_object(signature, right)?
        )),
        TermKind::Case(left, right) => Ok(format!(
            "case({}, {})",
            fmt_term(signature, left)?,
            fmt_term(signature, right)?
        )),
        TermKind::Curry(inner) => Ok(format!("curry({})", fmt_term(signature, inner)?)),
        TermKind::Eval(domain, codomain) => Ok(format!(
            "eval[{}, {}]",
            fmt_object(signature, domain)?,
            fmt_object(signature, codomain)?
        )),
    }
}

fn fmt_morphism(signature: &Signature, morphism: &Morphism) -> Result<String, FormatError> {
    match morphism.kind() {
        MorphismKind::Generator(id) => Ok(generator_name(signature, id)?.to_owned()),
        MorphismKind::Id => Ok(format!("id[{}]", fmt_object(signature, morphism.source())?)),
        MorphismKind::Compose(left, right) => Ok(format!(
            "({} >>> {})",
            fmt_morphism(signature, left)?,
            fmt_morphism(signature, right)?
        )),
        MorphismKind::Discard => Ok(format!(
            "discard[{}]",
            fmt_object(signature, morphism.source())?
        )),
        MorphismKind::Absurd => Ok(format!(
            "absurd[{}]",
            fmt_object(signature, morphism.target())?
        )),
        MorphismKind::First => {
            let (left, right) = expect_product(morphism.source(), "first source")?;
            Ok(format!(
                "first[{}, {}]",
                fmt_object(signature, left)?,
                fmt_object(signature, right)?
            ))
        }
        MorphismKind::Second => {
            let (left, right) = expect_product(morphism.source(), "second source")?;
            Ok(format!(
                "second[{}, {}]",
                fmt_object(signature, left)?,
                fmt_object(signature, right)?
            ))
        }
        MorphismKind::Pair(left, right) => Ok(format!(
            "pair({}, {})",
            fmt_morphism(signature, left)?,
            fmt_morphism(signature, right)?
        )),
        MorphismKind::Left => {
            let (left, right) = expect_coproduct(morphism.target(), "left target")?;
            Ok(format!(
                "left[{}, {}]",
                fmt_object(signature, left)?,
                fmt_object(signature, right)?
            ))
        }
        MorphismKind::Right => {
            let (left, right) = expect_coproduct(morphism.target(), "right target")?;
            Ok(format!(
                "right[{}, {}]",
                fmt_object(signature, left)?,
                fmt_object(signature, right)?
            ))
        }
        MorphismKind::Case(left, right) => Ok(format!(
            "case({}, {})",
            fmt_morphism(signature, left)?,
            fmt_morphism(signature, right)?
        )),
        MorphismKind::Curry(inner) => Ok(format!("curry({})", fmt_morphism(signature, inner)?)),
        MorphismKind::Eval => {
            let (exp, domain) = expect_product(morphism.source(), "eval source")?;
            let ObjectKind::Exponential(a, b) = exp.kind() else {
                return Err(FormatError::IllFormedMorphism(
                    "eval source left factor is not an exponential",
                ));
            };
            if a != domain {
                return Err(FormatError::IllFormedMorphism(
                    "eval source domain mismatch",
                ));
            }
            if b != morphism.target() {
                return Err(FormatError::IllFormedMorphism("eval target mismatch"));
            }
            Ok(format!(
                "eval[{}, {}]",
                fmt_object(signature, a)?,
                fmt_object(signature, b)?
            ))
        }
    }
}

fn expect_product<'a>(
    object: &'a Object,
    what: &'static str,
) -> Result<(&'a Object, &'a Object), FormatError> {
    match object.kind() {
        ObjectKind::Product(left, right) => Ok((left, right)),
        _ => Err(FormatError::IllFormedMorphism(what)),
    }
}

fn expect_coproduct<'a>(
    object: &'a Object,
    what: &'static str,
) -> Result<(&'a Object, &'a Object), FormatError> {
    match object.kind() {
        ObjectKind::Coproduct(left, right) => Ok((left, right)),
        _ => Err(FormatError::IllFormedMorphism(what)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::check;
    use crate::object_expr::ObjectExpr;
    use crate::signature::SignatureBuilder;
    use crate::term::Term;

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

    fn name(text: &str) -> crate::name::Name {
        crate::name::Name::new(text).expect("valid")
    }

    #[test]
    fn formats_objects_with_explicit_association() {
        let signature = number_signature();
        let number = signature
            .base(signature.base_id("Number").unwrap())
            .unwrap();
        let left = signature
            .product(
                &signature.product(&number, &number).unwrap(),
                &signature.unit(),
            )
            .unwrap();
        let right = signature
            .product(
                &number,
                &signature.product(&number, &signature.unit()).unwrap(),
            )
            .unwrap();
        assert_eq!(
            format_object(&signature, &left).unwrap(),
            "((Number × Number) × Unit)"
        );
        assert_eq!(
            format_object(&signature, &right).unwrap(),
            "(Number × (Number × Unit))"
        );
        let exp = signature.exponential(&number, &number).unwrap();
        assert_eq!(
            format_object(&signature, &exp).unwrap(),
            "(Number ⇒ Number)"
        );
    }

    #[test]
    fn formats_term_and_typed_morphism() {
        let signature = number_signature();
        let two = Term::generator(&signature, signature.generator_id("two").unwrap()).unwrap();
        let three = Term::generator(&signature, signature.generator_id("three").unwrap()).unwrap();
        let add = Term::generator(&signature, signature.generator_id("add").unwrap()).unwrap();
        let program = Term::compose(
            &signature,
            &Term::pair(&signature, &two, &three).unwrap(),
            &add,
        )
        .unwrap();
        assert_eq!(
            format_term(&signature, &program).unwrap(),
            "(pair(two, three) >>> add)"
        );
        let morphism = check(&signature, &program).unwrap();
        assert_eq!(
            format_typed_morphism(&signature, &morphism).unwrap(),
            "(pair(two, three) >>> add) : Unit ⟶ Number"
        );
    }

    #[test]
    fn distinguishes_arrow_from_exponential() {
        let signature = number_signature();
        let number = signature
            .base(signature.base_id("Number").unwrap())
            .unwrap();
        assert_eq!(
            format_arrow(&signature, &signature.unit(), &number).unwrap(),
            "Unit ⟶ Number"
        );
        assert!(
            format_object(
                &signature,
                &signature.exponential(&number, &number).unwrap()
            )
            .unwrap()
            .contains('⇒')
        );
        assert!(
            !format_arrow(&signature, &number, &number)
                .unwrap()
                .contains('⇒')
        );
    }

    #[test]
    fn rejects_cross_signature_format() {
        let left = number_signature();
        let right = number_signature();
        let err = format_object(&left, &right.unit()).expect_err("mismatch");
        assert!(matches!(err, FormatError::SignatureMismatch { .. }));
    }

    #[test]
    fn identical_structure_formats_identically_across_contexts() {
        let left = number_signature();
        let right = number_signature();
        let l = left
            .product(
                &left.unit(),
                &left.base(left.base_id("Number").unwrap()).unwrap(),
            )
            .unwrap();
        let r = right
            .product(
                &right.unit(),
                &right.base(right.base_id("Number").unwrap()).unwrap(),
            )
            .unwrap();
        assert_eq!(
            format_object(&left, &l).unwrap(),
            format_object(&right, &r).unwrap()
        );
    }
}
