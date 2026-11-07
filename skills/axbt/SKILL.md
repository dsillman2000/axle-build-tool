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

Assumed installed on the user's system (the intended way to use axbt is
as a uv tool; `uvx --from git+https://github.com/dsillman2000/axle-build-tool axbt …`
runs it without installing):

```bash
uv tool install git+https://github.com/dsillman2000/axle-build-tool
uv tool upgrade axle-build-tool   # occasionally
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
  # minify: false                 # optional: opt out of payload minification
modules:
  Core:
    dir: "Core"                     # module = directory of .lean files
    # `targets:` is deprecated (still honoured as a filter, with a
    # run-start warning). Bare runs already cover every file.
axle:
  environment: "lean-4.35.0"        # optional; defaults to latest offered
  timeout_seconds: 120
```

Guidance for structuring Lean code:

- **Small, single-purpose files.** Each file holds a few related
  declarations; `import` siblings by their file stem (`import Basics`).
  Imports must form a DAG — axbt parses them and topologically orders
  everything.
- **Files are the unit of execution.** A bare `axbt check` / `verify` /
  `build` judges every `.lean` file in every configured module, ordered
  along the import DAG (dependencies first). `targets:` is deprecated and
  still works as a filter; `--select` is the general narrowing mechanism.
  Helper declarations are validated as dependencies of the files that
  reference them.
- State axioms/settings at the top of files as usual — payload assembly
  flattens files with dependencies inlined, so a target always checks in
  full context.

## The iteration loop

Work from the project root (axbt writes `.axbt/` there — a compact
single-line `manifest.json` cache, inspectable payloads under `compiled/`,
and failing submissions under `failed/`; gitignore it. `compile` prunes
`compiled/` files whose source files are gone — "cache dir ⊋ manifest ⇒
delete" — while `failed/` payloads survive recompiles untouched).

1. **Edit** the Lean source.
2. **`axbt compile`** — scan, detect changes (MD5), extract declarations via
   the API. Incremental: unchanged files make no API calls.
3. **`axbt build`** — both tiers in one run, dbt-style: the check pass
   streams first, then the verify pass skips the selections whose check
   failed, and the run exits nonzero if either tier failed. Build-mode rows
   carry a `[check]`/`[verify]` suffix so the passes tell apart.
4. **`axbt check`** alone for fast typechecking of every file. A file
   whose declarations all already carry a matching `checked_sig` is
   skipped (`OK (cached)`); `--force` re-checks everything. Errors
   print with positions attributed back to real source files. Iterate
   here; this tier is cheap and delta-cached.
5. **`axbt verify`** alone for kernel-level proof validation of finished
   proofs: rejects `sorry`, missing proofs, and axiom-dependence. Results
   are cached per declaration (keyed on file content + environment +
   options); re-runs skip anything still valid. Pass `--force` to re-verify.
   `axbt check` uses the same delta cache on `checked_sig`.
6. **`axbt list`** — the parsed declaration tree with `sorry` markers and
   file-accurate positions. Offline; use for orientation. `axbt graph`
   renders the same manifest as an interactive HTML dependency graph,
   colored per declaration by its check/verify stamp state — also offline.

Key semantics when advising the user:

- **check ≠ proof validation.** A `sorry` typechecks (warning only), so a
  green `check` means "compiles", not "proven". Only `verify` certifies.
  A genuinely sorried target shows its `sorry` warning in check output.
- **`--select` narrows the run** without changing config:
  `--select Core` (module) / `--select Core.Algebra` (file) /
  `--select Core.Algebra.ring_identity` (declaration; unique suffixes
  allowed). Declaration-level selects must name a theorem/lemma — check
  defs via their file or module.
- **`--sorry <selector>` (repeatable) grants a dependency subtree**:
  theorem proof bodies become `sorry` for that run — statements intact, so
  downstream work continues before the upstream is finished, and complete
  upstream proofs don't need re-certifying every run. Def/abbrev bodies
  always stay real (downstream proofs unfold them definitionally:
  anonymous constructors, projections, `rfl`). Selections inside a grant
  are skipped as "taken as granted". On verify, granted stubs are named to
  the API's `permitted_sorries` and never recorded as verified.
- **`--permitted-sorries <selector>`** (verify only) excuses a genuinely
  incomplete (sorried-in-source) declaration *without stubbing anything*.
  Use it when the upstream's proofs exist but are sorried; use `--sorry`
  when you want complete-but-untrusted upstreams treated as axioms.
- **`--fail-fast`** stops at the first failing selection (cancel in-flight
  submissions); under `build`, a fail-fast in the check pass abandons the
  build before verifying.
- **`--force`** (check/verify/build) re-judges every selection even when
  all declarations already carry a valid stamp, bypassing the delta cache.
  `build` passes it to both tiers.
- **Minification is on by default**: comments, docstrings, and blank lines
  are stripped from submitted payloads (structural indentation survives;
  attribution stays exact). `--no-minify` opts a run out;
  `project.minify: false` changes the default.
- **Failing submissions persist automatically** (issue 42's debugging
  workflow): on a FAIL verdict, the exact submitted content (minified and
  trimmed as sent — the shape the printed coordinates refer to) is written
  to `.axbt/failed/<request-id>.lean`, with `<request-id>.map.json` carrying
  the payload→source position map (sections, per-section source line lists,
  node→source paths, tier, request id). The FAIL row names both paths, and
  attributable diagnostics carry the covering declaration:
  `<file>:<line> ... (declaration 'name')`. Nothing persists on OK or SKIP,
  failures of repeat runs accumulate side by side (keyed on request id),
  and recompiles never prune `failed/`. This makes FAIL-span autopsies a
  local, offline operation — no dependency on `--share`'s web UI.
- **`--share`** (check/verify/build) prints a web link to that exact run —
  check runs open the check UI, verify runs the verify_proof UI. Best
  effort; never affects exit codes.
- **`axbt debug`** is the first stop when anything seems off (key,
  environment, cache state).

## Typical agent workflow

- Scaffold: `axbt init my-proofs`, then edit `axbt_project.yml` and the
  module sources.
- After edits: run `axbt build` (or `axbt check` /
  `axbt check --select <file>` while iterating) and read attributed errors
  back to the user; fix Lean code; repeat.
- When a proof looks complete: `axbt build`'s verify pass — or a bare
  `axbt verify` — is the authoritative verdict; iterate on the Lean
  source, not the tool.
- To prove a new theorem while an upstream file is still unfinished:
  `axbt build --sorry <upstream-file>` (grants apply in both passes), or
  `--permitted-sorries <selector>` when only that one declaration is
  sorried in source.
- When a FAIL needs investigating (usually reading attributed positions
  isn't enough — e.g. out-of-reach span positions like a `whnf` timeout,
  or a composition/shape question that doesn't reproduce from source):
  read the failing run's `.axbt/failed/<request-id>.lean` — the exact
  bytes the API saw — and walk its coordinates through `.map.json`
  (`line_map` per section → original file lines; `paths` names the
  files). The report line above the diagnostics already names the paths.
  Deterministic failures persist the same content on every retry, so an
  unrelated edit (run again, fail again) still gets a fresh request id.
- When tidying a project (files deleted, stems renamed): `compile` (or
  `--full-refresh`) prunes the dead payloads from `.axbt/compiled/` and
  prints what it pruned; if a stale `--select` on a former file stem
  reports "no file stem matches", the manifest is already right — the
  old cache artifact was the only residue, and the same run removes it.
- Before claiming success to the user: the success criterion for a Lean
  project here is the verify tier exiting 0 (i.e. `axbt verify` or
  `axbt build` exiting 0) — a green `check` is not sufficient on its own.
