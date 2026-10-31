---
name: axbt
description: |
  Drive axbt — a dbt-style build/check/verify tool for Lean 4 projects that
  runs everything through the Axle (Axiom Lean Engine) API. Load when the user
  mentions axbt, works in a project containing axbt_project.yml, or wants to
  structure a Lean project, typecheck, or rigorously verify proofs via the API
  (no local Lean install needed).
---

# axbt — structured Lean 4 development via the Axle API

axbt orchestrates a Lean 4 project as a dependency DAG of small files, and
submits self-contained payloads to the Axle API for checking and
kernel-level proof verification. No local Lean/Mathlib install is needed.

Assumed installed on the user's system:

```bash
uv tool install git+https://github.com/dsillman2000/axle-build-tool
uv tool upgrade axbt   # occasionally
```

It requires `AXLE_API_KEY` in the environment. Verify setup any time with
`axbt debug` (key acceptance, resolved environment, cache state).

## Project anatomy

Scaffold new projects with `axbt init PATH` (config + starter module). A
project is a directory with `axbt_project.yml` and one directory per module
of plain `.lean` files:

```yaml
project:
  name: "MyProject"
modules:
  Core:
    dir: "Core"                     # module = directory of .lean files
    targets:                        # the declarations that matter
      - Basics.semantics
      - Algebra.ring_identity
axle:
  environment: "lean-4.35.0"        # optional; defaults to latest offered
  timeout_seconds: 120
```

Guidance for structuring Lean code:

- **Small, single-purpose files.** Each file holds a few related
  declarations; `import` siblings by their file stem (`import Basics`).
  Imports must form a DAG — axbt parses them and topologically orders
  everything.
- **Targets are the point.** `targets` lists the theorems/lemmas whose
  correctness the project exists to establish. Helper lemmas don't need
  target entries; they're validated as dependencies. Verify runs target
  every PR-style gate; check uses them as the default selection.
- State axioms/settings at the top of files as usual — payload assembly
  flattens files with dependencies inlined, so a target always checks in
  full context.

## The iteration loop

Work from the project root (axbt writes `.axbt/` there — cache + manifest;
gitignore it).

1. **Edit** the Lean source.
2. **`axbt compile`** — scan, detect changes (MD5), extract declarations via
   the API. Incremental: unchanged files make no API calls.
3. **`axbt check`** — fast typechecking of every target. Errors print with
   positions attributed back to real source files. Iterate here; this tier
   is cheap and always re-submits.
4. **`axbt verify`** — kernel-level proof validation for finished proofs:
   rejects `sorry`, missing proofs, and axiom-dependence. Results are cached
   per declaration (keyed on file content + environment); re-runs skip
   anything still valid. Pass `--force` to re-verify everything.
5. **`axbt list`** — the parsed declaration tree with `sorry` markers and
   file-accurate positions. Offline; use for orientation.

Key semantics when advising the user:

- **check ≠ proof validation.** A `sorry` typechecks (warning only), so a
  green `check` means "compiles", not "proven". Only `verify` certifies.
  A genuinely sorried target shows its `sorry` warning in check output.
- **`--select` narrows the run** without touching `targets`:
  `--select Core` (module) / `--select Core.Algebra` (file) /
  `--select Core.Algebra.ring_identity` (declaration; unique suffixes
  allowed). Declaration-level selects must name a theorem/lemma — check
  defs via their file or module.
- **`--sorry <selector>` (repeatable) stubs a dependency subtree**: proof
  bodies become `sorry` for that run so downstream work continues before
  the upstream is finished. Selections inside a `--sorry` grant are
  skipped as "taken as granted". On verify, excused stubs are named to
  the API's `permitted_sorries` and never recorded as verified.
- **`--permitted-sorries <selector>`** (verify only) excuses a genuinely
  incomplete declaration without stubbing it.
- **`--share`** (check/verify) prints a web link to that exact run — the
  right thing to paste when asking someone to look at a failure. Best
  effort; never affects exit codes.
- **`axbt debug`** is the first stop when anything seems off (key,
  environment, cache state).

## Typical agent workflow

- Scaffold: `axbt init my-proofs`, then edit `axbt_project.yml` and the
  module sources.
- After edits: run `axbt compile` then `axbt check` (or
  `axbt check --select <file>`) and read attributed errors back to the
  user; fix Lean code; repeat.
- When a proof looks complete: `axbt verify` — treat a FAIL as the
  authoritative verdict and iterate on the Lean source, not the tool.
- To prove a new theorem while an upstream lemma is still unfinished:
  `axbt check --sorry <upstream-file>` (and the same on verify with
  `--permitted-sorries` if only that one declaration is incomplete).
- Before claiming success to the user: the success criterion for a Lean
  project here is `axbt verify` exiting 0 — a green `check` is not
  sufficient on its own.
