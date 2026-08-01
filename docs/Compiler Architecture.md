**Status:** Architectural direction  
**Current implementation target:** Rust Phase 0 kernel with Lean 4 metatheory

---

## Architectural Principle

The compiler must retain categorical information for as long as that information remains useful.

It must not immediately lower programs into generic control flow and erase the structures that justify:

- Typing
- Composition
- Equality
- Universal properties
- Interpretation
- Derivation
- Verification
- Optimization

The intended long-term pipeline is:

1. Parse source syntax
2. Resolve declarations and names
3. Resolve transparent aliases
4. Infer source-level types
5. Elaborate into explicit semantic structures
6. Check core terms
7. Produce trusted typed morphisms
8. Simplify categorical structure where useful
9. Decide definitional equality
10. Verify proof and law evidence
11. Elaborate values, computations, effects, and resources into their categorical layers
12. Select runtime representations
13. Lower through verified or explicitly trusted functors
14. Produce control-flow IR
15. Perform machine-level optimization
16. Generate executable code

Phase 0 implements only the pure bicartesian-closed subset.

---

## Semantic Layers

The architecture must distinguish:

```text
mathematical semantics
```

from:

```text
compiler representation
```

and from:

```text
runtime representation
```

For example:

- A categorical model is not a Rust trait.
- A product object is not inherently a heap struct.
- A coproduct is not inherently a tagged machine union.
- An exponential is not inherently one closure representation.
- A runtime callback is not the definition of a pure generator.

Implementation mechanisms may realize semantics.

They may not replace them.

---

## Phase 0 Languages and Tools

### Production kernel

Rust

### Metatheory and proofs

Lean 4

### Intended executable refinement

Verification-friendly Rust connected to Lean through Aeneas or another machine-checked path.

### Constraints on verified Rust

The verified equality path should avoid:

- `unsafe`
- Interior mutability
- Hidden global state
- Nondeterministic iteration
- Runtime model callbacks
- Unspecified hashing behavior
- Unverified foreign dependencies

---

## Phase 0 Inputs

The kernel receives:

- An unresolved signature description
- A fully explicit resolved core term
- Optionally, a trusted executable runtime model

The kernel does not initially require:

- Source parser
- Alias system
- Variable elaborator
- Type inference
- Source-level proof syntax

Early programs are built directly through the Rust API.

---

## Representation Layers

```text
ObjectExpr
- unresolved base names
- signature-construction input
        ↓ SignatureBuilder::build()

Signature + Object
- immutable
- resolved typed IDs
- exact signature context

Term
- explicit categorical syntax
- resolved
- structurally valid
- potentially ill typed
        ↓ check()

Morphism
- fully typed
- trusted
- exact source and target
```

Phase 1 adds:

```text
Source AST
- names
- aliases
- variables
- patterns
- source functions
- syntactic conveniences
        ↓ resolution, inference, elaboration

Term
```

Elaboration is structural and type directed.

It is not textual substitution.

---

## Core Object Representation

Conceptually:

```rust
pub struct Object(Arc<ObjectData>);

struct ObjectData {
    signature: SignatureContextId,
    node: ObjectNode,
}

enum ObjectNode {
    Base(BaseId),
    Unit,
    Never,
    Product(Object, Object),
    Coproduct(Object, Object),
    Exponential(Object, Object),
}
```

Properties:

- Opaque public handle
- Exhaustive internal enum
- Immutable shared nodes
- No null children
- No invalid field combinations
- Structural equality
- No semantic pointer equality
- No interior mutability

---

## Signature Construction

Signatures are built through a mutable builder and become immutable.

The builder:

1. Validates names.
2. Rejects duplicates.
3. Assigns deterministic typed IDs.
4. Resolves generator object expressions.
5. Rejects undeclared base references.
6. Computes a canonical fingerprint.
7. Creates a fresh exact context identity.

The compiler distinguishes:

```text
SignatureContextId
```

for one exact in-memory context, and:

```text
SignatureFingerprint
```

for stable canonical contents.

Checked IR from different contexts cannot be mixed directly.

---

## Core Terms

Conceptually:

```rust
pub struct Term(Arc<TermData>);

struct TermData {
    signature: SignatureContextId,
    node: TermNode,
}
```

Term variants contain explicit object indices where required.

Terms may represent ill-typed compositions and branch mismatches so that the checker can produce diagnostics.

Terms may not contain:

- Unresolved names
- Missing children
- Invalid variants
- Cross-signature objects
- Cross-signature generators

---

## Checked Morphisms

Conceptually:

```rust
pub struct Morphism(Arc<MorphismData>);

struct MorphismData {
    signature: SignatureContextId,
    source: Object,
    target: Object,
    node: MorphismNode,
}
```

Each checked child is itself a `Morphism`.

Checked node variants omit redundant object indices already determined by the enclosing arrow.

Only trusted constructors create `Morphism`.

Trusted constructors derive arrow types from operands rather than accepting arbitrary claimed types.

Internal inconsistency produces `KernelFault`.

---

## Type Checker

The checker:

- Validates signature context
- Implements every typing rule
- Computes exact source and target objects
- Requires structural equality at composition boundaries
- Validates pairing
- Validates case analysis
- Validates currying
- Validates evaluation
- Produces a separate checked tree
- Never inserts structural isomorphisms
- Never invokes source-level inference

---

## Sound Simplifier

The simplifier performs only trusted bicartesian-closed rewrites.

It may support:

- Composition reassociation
- Identity elimination
- Product beta and eta
- Coproduct beta and eta
- Exponential beta and eta
- Terminal uniqueness
- Initial uniqueness

It must not:

- Use user laws
- Use model equations
- Inspect generator implementations
- Insert canonical isomorphisms
- Claim completeness for definitional equality

The simplifier is an optimizer and inspection tool.

---

## Verified Equality

Definitional equality is implemented through a private equality calculus and saturated focusing.

Conceptually:

```text
Morphism
    ↓ categorical translation
typed equality term
    ↓ focusing and saturation
focused saturated form
    ↓ verified comparison
Boolean result
```

The public semantic IR remains categorical.

Lean must prove that this result agrees exactly with equality in the syntactic category.

The Rust equality implementation must refine the verified algorithm.

---

## Abstract Interpretation

The mathematical interpreter is the unique structure-preserving functor induced by the free-category theorem.

This level is independent of Rust.

Compiler architecture must treat abstract interpretation as the source of semantic correctness for:

- Identity
- Composition
- Products
- Coproducts
- Exponentials
- Generators

---

## Runtime Interpreter

The Phase 0 runtime uses object-tagged dynamic values.

Conceptually:

```rust
pub struct Value {
    object: Object,
    repr: Arc<ValueRepr>,
}
```

The interpreter owns:

- Unit
- Products
- Coproducts
- Functions
- Application
- Structural validation

A runtime model owns:

- Opaque base payloads
- Generator implementations

Before and after generator calls, the interpreter verifies object tags.

A contract violation is a `ModelFault`.

The runtime representation is one executable realization of abstract semantics.

---

## Future Pure Source Elaboration

Phase 1 source elaboration translates:

- Variables into projections
- Tuples into pairing
- Pattern matching into case analysis
- Lambdas into currying
- Application into pairing and evaluation
- Aliases into resolved object structure
- Records into labeled product structure
- Variants into labeled coproduct structure

Genuine polymorphism is not assumed to elaborate directly into the monomorphic core.

Early generic syntax may monomorphize.

---

## Future Value and Computation Layers

Before effects, the compiler must introduce an explicit semantic distinction between:

- Pure values
- Effectful computations

The architecture must define:

- Their categories
- Evaluation strategy
- Function spaces
- Connecting functors or adjunctions
- How handlers operate
- How pure morphisms embed into computations

This cannot be left as an implicit runtime convention.

---

## Future Resource Layer

Persistent pure objects remain cartesian.

Resource-sensitive objects require a separate noncartesian layer.

The compiler architecture should support:

```text
persistent value category
    ↕ explicit modality / adjunction
resource-sensitive monoidal category
```

Duplication and discarding of resources must be governed by structure, not special-case checker bans on ordinary product operations.

---

## Future Effect Layer

First-order algebraic effects use free algebraic constructions.

Scoped and higher-order effects require generalized representations.

The compiler must represent effect structure explicitly until it is:

- Handled
- Interpreted
- Transformed
- Lowered
- Proven safe

No effect may be hidden inside a supposedly pure generator or morphism.

---

## Future Recursive Data Layer

Recursive data must distinguish:

- Strictly positive functor definitions
- Initial algebras
- Terminal coalgebras
- Iso-recursive structure
- Equi-recursive equality
- Folds
- Unfolds
- Termination
- Productivity

The compiler must not add unrestricted recursive object equations as a convenience.

---

## Future Equality Layers

The compiler must maintain separate mechanisms for:

- Kernel definitional equality
- User-proven equality
- Model-relative observational equality
- Trusted assertions
- Optimizer facts
- Quotient theories

Only kernel definitional equality may be used implicitly by core checking.

---

## User-Defined Categories

External category declarations and internal category values remain distinct.

External declarations may be checked by the compiler before the language has the universes required for internal categories.

Internal categories require a separate universe and indexed-type design.

---

## Lowering

Every semantic lowering must identify what it preserves.

Preferred structure:

```text
source semantic category
    ↓ functor or verified interpretation
target semantic category
    ↓ representation selection
runtime IR
```

The destination is machine-checked preservation where feasible.

Explicit trust is permitted temporarily but must remain visible.

---

## Typed Metaprogramming

Typed elaborators may eventually construct:

- Objects
- Terms
- Morphisms
- Categories
- Functors
- Effects
- Proofs
- Typed IR

Generated terms must pass through the trusted kernel.

Compiler extensions may propose transformations.

They may not bypass checking or equality verification.

The preferred architecture remains:

```text
untrusted generation or search
    +
small trusted verification
```