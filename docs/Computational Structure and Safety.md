**Status:** Future semantic guardrails  
**Purpose:** Define constraints for adding effects, resources, recursion, concurrency, polymorphism, and unsafe execution without breaking categorical coherence.

---

## 1. Purpose

The Phase 0 core describes persistent total pure values and transformations.

A practical programming language also needs:

- Effects
- Failure
- Nontermination
- Resources
- Memory
- Concurrency
- Foreign interaction
- Recursive data
- Generic programming

These features must not be inserted as exceptions to the pure bicartesian-closed semantics.

Each requires an explicit semantic layer and a precise connection to the existing core.

---

## 2. Persistent Pure Values

The Phase 0 category is cartesian.

Every object therefore supports canonical:

```text
duplicate : A ⟶ A × A
discard   : A ⟶ Unit
```

This is appropriate for persistent values that may be copied and forgotten without semantic consequences.

Examples include:

- Immutable numbers
- Immutable text
- Persistent records
- Pure algebraic data
- Pure functions

---

## 3. Resource-Sensitive Values

Resources such as these cannot be unrestricted cartesian values:

- File handles
- Sockets
- Unique buffers
- Locks
- Transactions
- Device handles
- Linear capabilities
- Values with required cleanup

Duplicating or discarding them may be invalid.

Resource semantics therefore require a noncartesian category.

The preferred direction is a linear/nonlinear architecture with:

- A cartesian category of persistent values
- A symmetric monoidal closed category of resource-sensitive values
- Explicit functors or an adjunction connecting them
- A modality controlling which resources may be duplicated or discarded

Ownership and borrowing must emerge from this structure or another equally precise categorical discipline.

---

## 4. Cleanup and Lifetime Semantics

Resource safety must account for:

- Acquisition
- Scope
- Use
- Transfer
- Borrowing
- Cleanup
- Cancellation
- Exceptional paths
- Partial execution
- Program termination

Cleanup may not rely only on informal conventions or backend destructors.

The semantic layer must explain why cleanup occurs exactly when required.

Potential tools include:

- Linear types
- Affine types
- Regions
- Capabilities
- Scoped handlers
- Linear continuations
- Resource algebras

No mechanism is selected yet.

---

## 5. Values and Computations

Effects require an explicit distinction between values and computations.

The language must define:

- What counts as a value
- What counts as a computation
- How pure values embed into computations
- How functions consume and produce computations
- Evaluation order
- Sequencing
- Thunks or suspensions, if any
- Handler semantics

A call-by-push-value-style architecture is a candidate because it makes this distinction explicit and categorical.

The final choice remains open.

---

## 6. First-Order Algebraic Effects

First-order algebraic effect signatures define operations such as:

```text
print : Text ⟶ Unit
read  : Unit ⟶ Text
```

Their computational structure should arise from a free algebraic construction.

Handlers provide interpretations of the generated structure.

The system must specify:

- Effect signatures
- Effect collections
- Operation invocation
- Resumptions
- Handler typing
- Effect elimination
- Effect transformation
- Forwarding
- Handler composition

---

## 7. Scoped and Higher-Order Effects

Some effects contain or delimit computations.

Examples:

- `local`
- `bracket`
- Transactions
- Exception masking
- Structured concurrency
- Parallel composition
- Cancellation scopes
- Resource regions

These are not assumed to be ordinary first-order algebraic operations.

They require scoped, higher-order, indexed, or related generalized constructions.

The implementation may not force them into an incorrect first-order encoding merely for uniform syntax.

---

## 8. Failure

Pure morphisms do not fail.

Recoverable failure may be represented through:

- Coproducts such as `Result`
- Explicit error effects
- Another computation-layer structure

Foreign exceptions and host panics are not language-level failures unless explicitly translated.

Uncontained host failure is a runtime trust violation.

---

## 9. Nontermination

Pure Phase 0 morphisms terminate.

Potential nontermination requires an explicit computation type or effect.

Possible categorical models include:

- Partiality monads
- Delay structures
- Coinductive computations
- Domain-theoretic semantics
- Algebraic effects for divergence

The choice remains open.

Unrestricted recursion may not masquerade as a pure morphism.

---

## 10. Recursive Data

Inductive data should arise from initial algebras of approved functors.

Initial support should focus on strictly positive polynomial functors.

Examples:

```text
NatF[X] = Unit + X
Nat     = μX. NatF[X]
```

```text
ListF[A, X] = Unit + A × X
List[A]     = μX. ListF[A, X]
```

The language must distinguish:

- Functor definition
- Positivity proof
- Fixed-point object
- Initial algebra
- Fold
- Structural recursion
- Iso-recursive roll and unroll
- Equi-recursive equality

Coinductive data similarly requires terminal coalgebras and productivity.

---

## 11. Parametric Polymorphism

Genuine parametric polymorphism is not simply repeated monomorphic syntax.

It may require:

- Indexed categories
- Fibrations
- Logical relations
- Relational parametricity
- Universes
- Quantification
- Natural transformations indexed by types

Early generic programming may use:

- Metalevel schemas
- Code generation
- Monomorphization

These mechanisms must be labeled accurately.

They are not first-class polymorphism.

---

## 12. Concurrency

Concurrency requires semantics for:

- Task creation
- Task composition
- Communication
- Shared state
- Cancellation
- Determinism
- Nondeterminism
- Data-race prevention
- Structured lifetimes
- Resource interaction

Possible structures include:

- Actors
- Session types
- Process categories
- Effectful tasks
- Monoidal composition
- Traced or compact structure
- Linear channels

No concurrency primitive should be added before its safety and compositional semantics are defined.

---

## 13. Memory Safety

The language must eventually choose how memory is managed.

Candidates include:

- Tracing garbage collection
- Ownership and borrowing
- Regions
- Reference counting
- Linear capabilities
- Hybrid systems

The choice must account for:

- Aliasing
- Mutation
- Cycles
- Closures
- Foreign memory
- Concurrency
- Resource cleanup
- Unsafe escape hatches

The categorical value/resource architecture must constrain this decision.

---

## 14. Foreign Interaction

Foreign functions must explicitly declare properties such as:

- Purity
- Totality
- Failure
- Effects
- Determinism
- Thread safety
- Memory safety
- Ownership transfer
- Callback behavior
- Panic or exception behavior

A foreign declaration is a trust boundary unless backed by proof or generated safe wrappers.

Unsafe foreign behavior must not inhabit the pure category silently.

---

## 15. Unsafe Operations

Unsafe programming may eventually exist.

Unsafe code must:

- Be syntactically visible
- Be semantically isolated
- State which invariants it assumes
- State which guarantees it may violate
- Produce safe abstractions only through checked boundaries
- Never rewrite foundational equality without proof

Unsafe is a controlled trust boundary, not a second hidden language.

---

## 16. Compile-Time Execution

Safe compile-time programs must terminate and respect effect restrictions.

Potentially dangerous compile-time work requires:

- Explicit capabilities
- Resource limits
- Sandboxing
- Unsafe markers
- Reproducibility rules

Compile-time execution must not bypass the trusted kernel or introduce untracked host effects.

---

## 17. Admission Requirement for Future Features

Before implementation, every major feature must document:

- Its category or categorical structure
- Its objects and morphisms
- Its laws
- Its universal property or semantic characterization
- Its connection to existing layers
- Its equality rules
- Its proof obligations
- Its runtime interpretation
- Its trust assumptions
- Its interaction with resources and effects

Features without this account remain research ideas rather than language commitments.