# Gimbal

Phase 0 work toward a free bicartesian-closed semantic kernel (Rust) with Lean 4 metatheory.

Design source of truth: the Obsidian vault folder linked in this workspace (`Projects/Gimbal`). Edit design notes there. Repo `docs/` holds implementation notes only (trusted base, module boundaries) — not a vault mirror.

## Workspace scaffold

This repository currently holds an **initial Phase 0A workspace scaffold**. It is intentionally minimal and revisable. It does not lock final crate, Lean-library, or Rust–Lean refinement boundaries.

| Path | Role |
| --- | --- |
| `crates/kernel` | Production semantic kernel library |
| `crates/cli` | Thin binary; dependency smoke test (not a source parser) |
| `lean/` | Lean 4 / Lake project stub |

## Toolchains (pinned)

- Rust: `1.97.1` via [`rust-toolchain.toml`](rust-toolchain.toml)
- Lean: `leanprover/lean4:v4.32.2` via [`lean/lean-toolchain`](lean/lean-toolchain)

Updates are deliberate commits, not floating `stable` channels.

## Local checks

```bash
cargo fmt --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo run -p gimbal_cli
```

```bash
cd lean
lake build
```

(Install [elan](https://github.com/leanprover/elan) if `lake` is missing; it will fetch the pinned Lean toolchain.)

## Implementation docs

- [Trusted base](docs/trusted-base.md)
- [Module boundaries](docs/module-boundaries.md)
- Agent rules: [`.cursor/rules/`](.cursor/rules/) (decision discipline; no panic-as-control-flow in `crates/kernel`)

## Next

Next: Lean core syntax (Milestone 4). See Phase 0 Implementation Plan in Obsidian.
