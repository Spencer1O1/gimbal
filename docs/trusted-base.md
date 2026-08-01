# Trusted Base

**Scope:** Implementation snapshot for the Phase 0A workspace scaffold.  
**Design authority:** Obsidian vault `Projects/Gimbal/` (linked workspace folder).

This file lists what the repository currently trusts. Anything that enters a verified path later must be added here deliberately.

## Present

| Component | Trust role |
| --- | --- |
| Rust compiler `1.97.1` (pinned in `rust-toolchain.toml`) | Builds the production kernel and CLI |
| Rust standard library for that toolchain | Used by kernel and CLI |
| Lean 4 kernel `v4.32.2` (pinned in `lean/lean-toolchain`) | Will check metatheory and equality proofs when they exist |
| Lake / Lean toolchain installer (elan) | Fetches and runs the pinned Lean |

## Kernel policy

- `unsafe` is forbidden in the workspace via `[workspace.lints.rust] unsafe_code = "forbid"`.
- Any future exception must be listed in this file with rationale and blast radius.

## Not yet present (named for later)

These are expected to become trusted when Phase 0B/0C verification lands. They are **not** trusted today because they are not in the tree:

- Aeneas (or replacement) translation / refinement tooling
- Charon (or replacement) Rust front-end for verification
- Any extracted or translated equality artifacts
- External crates on verified equality paths (none yet; none allowed without listing here)

## Runtime host

When a runtime model adapter exists, generator implementations are a trusted promise of totality and purity for the pure Phase 0 core. A dishonest host is a **model fault**, not a language effect. Document concrete host assumptions here when the adapter is introduced.

## External dependencies

The kernel currently has **no** external Rust crates. When fingerprinting, hashing, or other deps are added:

- List each crate and version here if it touches a verified or equality-critical path.
- Prefer keeping verified equality isolatable from optional runtime/CLI dependencies.
