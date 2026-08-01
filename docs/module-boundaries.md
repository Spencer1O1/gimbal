# Module Boundaries

**Scope:** Architectural constraints for the Phase 0 implementation scaffold.  
**Not:** A settled file-to-file dependency graph. Exact module arrows wait until the Rust APIs exist.

Design authority remains in the Obsidian vault `Projects/Gimbal/` (linked workspace folder).

## Constraints

1. **Unchecked terms never depend on the checker.** `Term` construction may produce ill-typed programs; checking is a separate step.
2. **Checked morphisms cannot be publicly constructed.** Outside the kernel’s trusted constructors / checking path, `Morphism` values are not forged.
3. **Only checking produces a public `Morphism`.** Application code and the CLI obtain morphisms by checking terms against a signature.
4. **Equality never depends on runtime models.** Definitional equality (Phase 0B) must remain isolatable from interpreters and host callbacks.
5. **Interpretation never changes or constructs semantic morphisms.** The runtime adapter evaluates; it does not elaborate new kernel morphisms.
6. **Runtime modules may depend on the checked kernel, never the reverse.** Kernel typing and equality do not import value/model/interpret layers.
7. **The CLI depends on public kernel APIs only.** The CLI is a dependency smoke test and future driver, not a back-door into private kernel guts.
8. **The verified equality path must be isolatable from runtime and CLI dependencies.** Crate splits may come later; the dependency direction must allow them.

## Provisional intuition (non-normative)

When modules appear, something like the following is expected — revise freely once APIs exist:

- Leaves: identifiers, names, errors
- Unresolved object syntax vs resolved objects vs signature builder are related but not a single linear chain
- Terms and morphisms both need objects and IDs; only `check` connects terms to public morphisms
- Simplification and formatting sit on checked structure
- Equality stays clear of runtime
- Interpret/model sit above the checked kernel

## Deliberately unsettled

This scaffold does **not** lock:

- Whether equality becomes its own Rust crate
- Whether Aeneas-compatible code needs a separate crate
- Final Lean library hierarchy
- Whether the runtime model adapter splits from the kernel
- Whether the CLI stays in this workspace long term
- Shared fixture packaging
