**Status:** Active research questions  
**Rule:** Resolved commitments belong in [[Projects/CategoryLanguage/Foundational Design Commitments|Foundational Design Commitments]]. This file contains only unresolved choices.

---

## Phase 0 Lean Representation

- Should checked morphisms be intrinsically or extrinsically typed in Lean?
- Should definitional equality use a quotient, setoid, or another representation?
- How should signature-indexed objects and morphisms be encoded?
- How should typed opaque generator constants be represented?
- What binder representation best supports the equality calculus?
- How should contexts be represented?
- Which portions of the formal syntax should be executable?
- How should proof terms remain readable and maintainable?

---

## Equality Procedure

- What exact saturated-focusing presentation should be formalized?
- What saturation invariant establishes completeness?
- How are invertible commuting conversions represented?
- Is comparison performed on canonical representatives or modulo a decidable relation?
- What termination measure is most suitable?
- What complexity bounds can be established?
- How should equality traces be exposed for debugging?
- What benchmark terms expose worst-case saturation behavior?

---

## Free Bicartesian Closed Category Proof

- What exact Lean definition of a category should be used?
- Should the project use Mathlib category theory or a smaller custom hierarchy?
- How should chosen products, coproducts, terminal, initial, and exponentials be encoded?
- What exact notion of strict bicartesian-closed functor should be used?
- How should the free-category universal property be stated?
- Should uniqueness be propositional equality of functors or structured equivalence?
- How should generator interpretations be indexed?
- How should the equality algorithm connect to equality in the syntactic category?

---

## Strict and Strong Models

- Is strict preservation sufficient for every intended Phase 0 use?
- When should strong preservation up to coherent isomorphism be introduced?
- What coherence data is required?
- Can strictification be used without complicating the implementation?
- How should non-`Set`-like models be demonstrated?

---

## Rust-to-Lean Verification

- Can the equality implementation remain within the Rust subset supported by Aeneas?
- Should Rust be translated into Lean, or should verified Lean code be extracted?
- What exact refinement theorem connects the executable result to the specification?
- Which translation artifacts should be committed?
- Which parts of Rust, Lean, Aeneas, Charon, and external libraries remain trusted?
- Should verified equality live in a separate crate?
- How should unsupported Rust features fail CI?
- Can allocation and `Arc` be abstracted away from the verified algorithm?
- Should the verified algorithm use owned trees, indices, arenas, or another representation?

---

## Phase 0 Engineering

- What exact workspace layout should be used?
- What canonical signature encoding defines fingerprints?
- Which stable hash algorithm should be used?
- Should structural hashes be cached?
- How should deeply nested terms avoid stack overflow?
- What deterministic format should display objects and morphisms?
- How should diagnostics preserve nested composition context?
- What error hierarchy distinguishes user errors, model faults, equality errors, and kernel faults?
- Should simplification use recursive traversal, explicit stacks, or composition spines?
- Should runtime values require `Send + Sync` initially?
- How should host panics be contained?
- What minimal runtime model best demonstrates opaque generators?

---

## Testing and Validation

- How should Rust and Lean share canonical fixtures?
- What depth-bounded generator should produce well-typed morphisms?
- Which generated properties supplement the formal proofs?
- How should differential tests compare Rust and Lean equality?
- What malformed-term fuzzing remains useful with opaque Rust enums?
- What performance tests should run on every commit?
- What resource limits should protect CI from equality blowups?
- How should simplifier interpretation preservation be tested?

---

## Phase 1 Source Language

- What should the first source syntax look like?
- Should composition use `>>>`?
- How should local variables elaborate into projections?
- How should lambdas elaborate into currying?
- How should application elaborate into pairing and evaluation?
- How should pattern matching elaborate into case analysis?
- How should records and variants elaborate?
- What syntax distinguishes aliases from nominal objects?
- How much inference should Phase 1 provide?
- When are annotations required?
- How should source aliases be preserved in diagnostics?
- How should elaborated categorical IR be displayed?
- What metalevel generic system should Phase 1 support?
- How should monomorphization be represented and cached?

---

## Recursive Data

- What syntax defines strictly positive functors?
- Which functor forms are accepted automatically?
- How is positivity checked?
- Should recursive data initially be iso-recursive?
- What explicit roll and unroll operations exist?
- When, if ever, is equi-recursive equality introduced?
- Which recursion schemes are primitive or derived?
- How are folds represented categorically?
- How is fusion verified?
- How are terminal coalgebras and productivity introduced?

---

## Value and Computation Semantics

- Should the language use call-by-push-value?
- What are the categories of values and computations?
- What adjunction or functorial relationship connects them?
- What is the evaluation order?
- How are computation-producing functions typed?
- How are thunks and forcing represented?
- How does the pure Phase 0 category embed?
- How does this interact with first-class functions and effects?

---

## First-Order Algebraic Effects

- What syntax declares operations?
- How are effects tracked?
- Are effect collections rows, sets, multisets, or indexed structures?
- How are duplicate effects represented?
- How are handlers typed?
- What restrictions apply to resumptions?
- How are effect transformations represented?
- Which laws are guaranteed by free construction?
- How are ordinary errors related to coproducts and error effects?

---

## Scoped and Higher-Order Effects

- What categorical construction represents scoped operations?
- How are computations passed to operations?
- How are resource scopes represented?
- How are `local`, masking, transactions, and cancellation typed?
- How do higher-order handlers compose?
- How are scoped effects lowered?
- Which features require linear resumptions or capabilities?

---

## Linear and Resource-Sensitive Semantics

- Should the resource category be symmetric monoidal closed?
- Should the language use linear or affine typing?
- What is the exact linear/nonlinear adjunction?
- What does the duplication modality mean?
- Which values may cross between persistent and resource layers?
- How are borrows represented?
- How are lifetimes represented?
- How is cleanup proved?
- How do effects and cancellation interact with resources?
- Is garbage collection compatible with the selected resource model?
- Where does unsafe memory access live?

---

## Genuine Parametric Polymorphism

- What categorical semantics should be used?
- Are universes required before polymorphism?
- Should the system use indexed categories or fibrations?
- How is relational parametricity expressed?
- What kind of universal quantification is supported?
- Is impredicativity allowed?
- How do polymorphic programs elaborate or compile?
- How does polymorphism interact with effects and resources?

---

## Equality and User Proofs

- What user-facing proof language should exist?
- Are equality proofs first-class?
- How are function equalities proven?
- How are quotient theories declared?
- How are user laws prevented from corrupting kernel equality?
- Can proven equalities guide optimization?
- How are observational equivalences stated relative to models?
- How are trusted declarations represented?
- Should custom rewrite systems require termination and confluence proofs?

---

## User-Defined Categories

- What is the first external category-declaration syntax?
- How are object families represented?
- How is `Hom[A, B]` represented?
- What proof obligations arise?
- How are external categories interpreted?
- When can categories become internal values?
- What universes are required?
- How are large categories represented?
- How are enriched, indexed, or internal categories added?
- How are interpreters distinguished from functors?

---

## Concurrency

- Are tasks effects, resources, processes, or another structure?
- How are tasks composed?
- How is structured concurrency represented categorically?
- How are channels typed?
- Are session types used?
- How are data races prevented?
- How are deterministic and nondeterministic concurrency distinguished?
- How does cancellation interact with resources and handlers?
- Can safe parallelization be derived from structure?

---

## Runtime and FFI

- What is the first compiled target?
- How are products, coproducts, and closures represented?
- How are foreign purity and totality claims expressed?
- How are foreign effects tracked?
- How is ownership transferred across FFI?
- How are callbacks represented?
- How are foreign exceptions and panics contained?
- Can wrappers supply machine-checkable evidence?
- How are foreign memory and lifetimes modeled?

---

## Tooling

- How should failed composition be explained?
- How should morphism graphs be visualized?
- Can source and diagrams remain synchronized?
- How should simplification steps be inspected?
- How should equality traces be presented?
- How should proof obligations be displayed?
- How should generated elaborations be navigated?
- What should the language server expose about universal constructions?
- Can tools show which category or semantic layer a value inhabits?