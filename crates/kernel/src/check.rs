//! Typing of [`Term`]s into trusted [`Morphism`]s.
//!
//! Emits detailed [`CheckError`]s for user-facing failures, then calls
//! [`Morphism`] constructors that independently enforce each typing rule.

use crate::error::CheckError;
use crate::morphism::Morphism;
use crate::object::ObjectKind;
use crate::signature::Signature;
use crate::term::{Term, TermKind};

/// Check `term` against `signature`, producing a trusted morphism.
pub fn check(signature: &Signature, term: &Term) -> Result<Morphism, CheckError> {
    let expected = signature.context_id();
    if term.signature_context() != expected {
        return Err(CheckError::SignatureMismatch {
            expected,
            actual: term.signature_context(),
        });
    }
    check_term(signature, term)
}

fn check_term(signature: &Signature, term: &Term) -> Result<Morphism, CheckError> {
    match term.kind() {
        TermKind::Generator(id) => {
            if signature.generator(id).is_err() {
                return Err(CheckError::InvalidGeneratorId(id));
            }
            Morphism::generator(signature, id).map_err(CheckError::Kernel)
        }
        TermKind::Id(object) => Morphism::id(signature, object).map_err(CheckError::Kernel),
        TermKind::Compose(left, right) => {
            let left_m = check_term(signature, left)?;
            let right_m = check_term(signature, right)?;
            if left_m.target() != right_m.source() {
                return Err(CheckError::ComposeMismatch {
                    left_target: left_m.target().clone(),
                    right_source: right_m.source().clone(),
                });
            }
            Morphism::compose(left_m, right_m).map_err(CheckError::Kernel)
        }
        TermKind::Discard(object) => {
            Morphism::discard(signature, object).map_err(CheckError::Kernel)
        }
        TermKind::Absurd(object) => Morphism::absurd(signature, object).map_err(CheckError::Kernel),
        TermKind::First(left, right) => {
            Morphism::first(signature, left, right).map_err(CheckError::Kernel)
        }
        TermKind::Second(left, right) => {
            Morphism::second(signature, left, right).map_err(CheckError::Kernel)
        }
        TermKind::Pair(left, right) => {
            let left_m = check_term(signature, left)?;
            let right_m = check_term(signature, right)?;
            if left_m.source() != right_m.source() {
                return Err(CheckError::PairSourceMismatch {
                    left_source: left_m.source().clone(),
                    right_source: right_m.source().clone(),
                });
            }
            Morphism::pair(signature, left_m, right_m).map_err(CheckError::Kernel)
        }
        TermKind::Left(left, right) => {
            Morphism::left(signature, left, right).map_err(CheckError::Kernel)
        }
        TermKind::Right(left, right) => {
            Morphism::right(signature, left, right).map_err(CheckError::Kernel)
        }
        TermKind::Case(left, right) => {
            let left_m = check_term(signature, left)?;
            let right_m = check_term(signature, right)?;
            if left_m.target() != right_m.target() {
                return Err(CheckError::CaseTargetMismatch {
                    left_target: left_m.target().clone(),
                    right_target: right_m.target().clone(),
                });
            }
            Morphism::case(signature, left_m, right_m).map_err(CheckError::Kernel)
        }
        TermKind::Curry(inner) => {
            let inner_m = check_term(signature, inner)?;
            if !matches!(inner_m.source().kind(), ObjectKind::Product(_, _)) {
                return Err(CheckError::CurrySourceNotProduct {
                    source: inner_m.source().clone(),
                });
            }
            Morphism::curry(signature, inner_m).map_err(CheckError::Kernel)
        }
        TermKind::Eval(domain, codomain) => {
            Morphism::eval(signature, domain, codomain).map_err(CheckError::Kernel)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn checks_pair_then_add() {
        let signature = number_signature();
        let two = Term::generator(&signature, signature.generator_id("two").unwrap()).unwrap();
        let three = Term::generator(&signature, signature.generator_id("three").unwrap()).unwrap();
        let add = Term::generator(&signature, signature.generator_id("add").unwrap()).unwrap();
        let paired = Term::pair(&signature, &two, &three).unwrap();
        let program = Term::compose(&signature, &paired, &add).unwrap();
        let morphism = check(&signature, &program).expect("well typed");
        let number = signature
            .base(signature.base_id("Number").unwrap())
            .unwrap();
        assert_eq!(morphism.source(), &signature.unit());
        assert_eq!(morphism.target(), &number);
    }

    #[test]
    fn rejects_ill_typed_composition() {
        let signature = number_signature();
        let two = Term::generator(&signature, signature.generator_id("two").unwrap()).unwrap();
        let add = Term::generator(&signature, signature.generator_id("add").unwrap()).unwrap();
        let bad = Term::compose(&signature, &two, &add).unwrap();
        let err = check(&signature, &bad).expect_err("ill typed");
        assert!(matches!(err, CheckError::ComposeMismatch { .. }));
    }

    #[test]
    fn checks_curry_of_add() {
        let signature = number_signature();
        let add = Term::generator(&signature, signature.generator_id("add").unwrap()).unwrap();
        let curried = Term::curry(&signature, &add).unwrap();
        let morphism = check(&signature, &curried).expect("well typed");
        let number = signature
            .base(signature.base_id("Number").unwrap())
            .unwrap();
        let exp = signature.exponential(&number, &number).unwrap();
        assert_eq!(morphism.source(), &number);
        assert_eq!(morphism.target(), &exp);
    }

    #[test]
    fn rejects_curry_of_non_product_source() {
        let signature = number_signature();
        let two = Term::generator(&signature, signature.generator_id("two").unwrap()).unwrap();
        let curried = Term::curry(&signature, &two).unwrap();
        let err = check(&signature, &curried).expect_err("ill typed");
        assert!(matches!(err, CheckError::CurrySourceNotProduct { .. }));
    }

    #[test]
    fn checks_eval() {
        let signature = number_signature();
        let number = signature
            .base(signature.base_id("Number").unwrap())
            .unwrap();
        let term = Term::eval(&signature, &number, &number).unwrap();
        let morphism = check(&signature, &term).expect("well typed");
        let exp = signature.exponential(&number, &number).unwrap();
        let source = signature.product(&exp, &number).unwrap();
        assert_eq!(morphism.source(), &source);
        assert_eq!(morphism.target(), &number);
    }
}
