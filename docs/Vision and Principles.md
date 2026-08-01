**Status:** Foundational  
**Purpose:** Define what the language is trying to become and the principles that constrain its design.

---

## Vision

This project aims to create a programming language in which category theory forms the actual semantic foundation.

Category theory will not merely describe selected library abstractions after the fact.

Programs will be understood primarily as morphisms.

Types and other computational domains will be understood as objects.

Programs will be assembled through composition, and programming constructs will arise from explicit categorical structures rather than unrelated compiler mechanisms.

The project may eventually use multiple related categories:

- A bicartesian closed category of persistent pure values
- Resource-sensitive monoidal categories
- Categories of effectful computations
- Kleisli or Eilenberg–Moore constructions
- Indexed or fibrational structures
- Categories of proofs, transformations, and compiler artifacts
- User-defined domain categories

Categorical unity does not require forcing every feature into one category.

It requires every layer to have precise semantics and explicit structure-preserving connections to the others.

The language should eventually make structures such as these concrete and useful:

- Categories
- Objects and morphisms
- Identity and composition
- Products and coproducts
- Terminal and initial objects
- Exponential objects
- Functors
- Natural transformations
- Adjunctions
- Monads and comonads
- Algebras and coalgebras
- Initial algebras and terminal coalgebras
- Recursion schemes
- Linear and nonlinear structure
- Kleisli categories
- Algebraic effects and handlers
- Scoped and higher-order effects
- Universal properties
- Commutative diagrams
- Equational reasoning
- User-defined computational categories
- Typed language construction

The objective is not to create a conventional functional language with categorical names.

The objective is to investigate what programming becomes when categorical structure is available to the programmer, type checker, compiler, optimizer, proof system, runtime, and development tools.

---

## Core Thesis

> Programs are typed morphisms, and composition is the primary means by which programs are constructed.

Given:

```text
f : A ⟶ B
g : B ⟶ C
```

their composition is:

```text
f >>> g : A ⟶ C
```

This composition must remain meaningful beyond parsing.

The compiler should retain knowledge that the result was constructed through composition and should be able to:

- Type-check it
- Explain it
- Simplify it
- Compare it
- Interpret it
- Verify it
- Optimize it
- Lower it while preserving meaning

Function application remains useful.

It arises from exponential structure rather than existing as a separate foundational semantic mechanism.

---

## Primary Design Values

### Simplicity

The language should have a small number of deep mechanisms.

There should not be several unrelated ways to represent the same idea.

Examples:

- Tuples and records arise from products.
- Variants and result types arise from coproducts.
- Pattern matching arises from coproduct elimination.
- Function values arise from exponential objects.
- Inductive data arise from initial algebras.
- First-order algebraic effects arise from free algebraic constructions.
- Domain-specific execution is expressed through interpreters, handlers, or functorial lowering.

Simplicity means conceptual unity, not pretending one construction covers structures it does not actually model.

### Safety

The language should make behavior honest in its types and categorical placement.

A pure morphism cannot secretly:

- Fail
- Panic
- Diverge
- Perform I/O
- Read time
- Use randomness
- Mutate external state
- Produce an invalid result

Potential failure, nontermination, and effects must be explicit.

The long-term language must also develop coherent systems for:

- Memory safety
- Resource and lifetime safety
- Concurrency and data-race safety
- Safe foreign-function interoperability
- Safe compile-time execution
- Controlled low-level escape hatches

Resource-sensitive values cannot be treated as unrestricted cartesian values.

Their semantics must prevent invalid duplication and discarding by construction.

### Categorical honesty

A feature does not count as categorical merely because it uses terms such as `Functor`, `Monad`, or `Morphism`.

A foundational feature must:

1. Correspond to a genuine categorical structure.
2. Have a precise semantic characterization.
3. State the laws it obeys.
4. Explain how it connects to existing language layers.
5. Be represented or recognized by the compiler.
6. Enable concrete composition, checking, derivation, interpretation, normalization, verification, or optimization.

When a feature lacks a precise categorical account, it is not ready to enter the language.

### Verification

The destination is machine-checked semantics and correctness by construction.

Important structures should be supported by evidence in this order:

1. Guaranteed by construction
2. Mechanically proven
3. Compiler-derived
4. Explicitly trusted
5. Tested
6. Unverified assertion

Tests remain valuable, but they do not substitute for proof of semantic claims.

### Practical execution

The language must eventually run real programs and interact with real systems.

Practicality does not justify adding semantically unrelated exceptions.

Instead, the design must find honest structures for:

- Effects
- Resources
- Concurrency
- Foreign interaction
- Compilation
- Runtime representation
- Unsafe operations

---

## What the Language Is Not

The language is not merely:

- A language where `map` is automatically inserted
- A language where every container implements a `Functor` interface
- Haskell with alternate syntax
- Rust with category-theory terminology
- A collection of category-inspired library functions
- A proof assistant disguised as a general-purpose language
- A purely academic notation with no execution model
- A language requiring formal diagrams for ordinary arithmetic
- A categorical vocabulary layer over a conventional compiler architecture
- A system that forces all resources and effects into an ordinary pure cartesian category
- An uncontrolled macro system that bypasses the trusted kernel

Categorically themed but semantically shallow features should be rejected.

---

## Progressive Depth

The same connected semantic architecture should support several levels of use.

### Ordinary programming

A programmer can write readable transformations, records, variants, functions, pattern matches, effects, and resource-safe code.

### Structural programming

A programmer can explicitly compose morphisms, define functors, use handlers, work with algebraic data, and inspect elaborated structure.

### Advanced categorical programming

A programmer can define:

- Natural transformations
- Categories
- Algebras
- Coalgebras
- Recursion schemes
- Interpreters
- Effect transformations
- Categorical compiler passes
- Linear and nonlinear interfaces

### Language construction

A library or compiler author can define:

- Domain-specific categories
- Typed syntax extensions
- Compile-time transformations
- Verified lowerings
- Proof-producing optimizations
- Domain-specific programming languages

Progressive depth must not create incompatible semantic systems.

Higher-level syntax must elaborate into existing verified structures or into explicitly introduced extensions.

---

## Universal Constructions Before Special Cases

When several language features arise from one universal construction, the language should implement the construction rather than hardcoding each feature separately.

Examples:

- Products generate projections and pairing.
- Coproducts generate injections and case analysis.
- Exponentials generate currying and evaluation.
- Initial algebras generate folds.
- Terminal coalgebras generate unfolds.
- First-order effect signatures generate free computational structures.
- Functors define structure-preserving compiler lowerings.

The user should state generators and essential structure.

The compiler should derive canonical lawful behavior whenever possible.

This principle does not permit applying a universal construction outside its valid scope.

Scoped, higher-order, resource-sensitive, or dependent features require their own honest structures.

---

## Equality Discipline

The language permanently separates:

### Definitional equality

Built into a trusted decidable kernel.

### Proven equality

Established by explicit proof evidence.

### Observational equality

Relative to a selected model or semantics.

### Trusted assertions

Accepted through a visible boundary when proof is unavailable.

User laws must not silently become definitional equality.

Model-specific optimizer facts must not alter the free foundational theory.

Quotients and theories with additional equations must be introduced explicitly.

---

## Models and Interpretation

The mathematical meaning of a model is categorical.

A model of a signature is not defined by a Rust trait or runtime representation.

A runtime interpreter is one executable realization of a categorical interpretation.

This separation prevents implementation choices such as dynamic values, host closures, or erased payloads from becoming language semantics.

---

## Laws Are Part of the Program

A categorical structure is not defined only by its operations.

Its laws are part of its meaning.

The language should distinguish laws that are:

- Guaranteed by construction
- Built into the trusted kernel
- Compiler-derived
- Mechanically proven
- Explicitly trusted
- Tested
- Unverified

Explicit trust may be necessary during development, but it must remain visible and may not silently justify correctness-critical transformations.

---

## Project Principles

### Semantics before syntax

Do not design attractive syntax for a concept whose semantics are not understood.

### Universal characterization before implementation

A foundational feature should state what mathematical object it constructs and what universal or semantic property characterizes it.

### Composition before application

Prefer designs that preserve composition as explicit analyzable structure.

### One connected semantic architecture

Surface conveniences may abbreviate the core.

New semantic layers must connect through explicit categorical constructions.

### Preserve information

Do not erase categorical structure before the compiler has used it.

### Theory must earn its complexity

An abstraction belongs only when it improves expressiveness, guarantees, implementation, or understanding.

### Practical execution matters

The language must eventually execute real programs and interact with real systems.

### Trust must be explicit

The compiler must distinguish proof, derivation, testing, trust, opacity, and unsafe behavior.

### Build the smallest honest core

The first implementation should be narrow but genuinely categorical.

### Do not confuse implementation with semantics

Rust types, runtime tags, storage layouts, and host callbacks are implementation mechanisms.

They do not define the mathematical language.

### Do not force structures where they do not fit

Persistent values, linear resources, effects, polymorphism, recursion, and concurrency may require different categories and connecting structure.

### Verify the destination

The project should progress from explicit trust toward machine-checked laws, universal properties, and implementations connected to verified specifications.