---
name: axbt
description: |
  Drive axbt — a dbt-style build/check/verify tool for Lean 4 projects that
  runs everything through the Axle (Axiom Lean Engine) API. Load when the user
  mentions axbt, works in a project containing axbt_project.yml, or wants to
  structure a Lean project, typecheck, verify proofs via the API (no local
  Lean install), or debug failing submissions from the .axbt/ artifacts.
---

# axbt — structured Lean 4 development via the Axle API

axbt orchestrates a Lean 4 project as a dependency DAG of small files and
submits self-contained payloads to the Axle API for typechecking and
kernel-level proof verification. No local Lean/Mathlib install is needed.

Axle is an external service managed by Axiom Math. Never script against the
API directly and never reach into axbt's service layer — every capability
flows through axbt's commands. The local `.axbt/` artifacts are axbt's own
output, always available offline, and covered here.

Install (intended as a uv tool; `uvx --from git+https://github.com/dsillman2000/axle-build-tool axbt …`
runs it ad hoc):

```bash
uv tool install git+https://github.com/dsillman2000/axle-build-tool
uv tool upgrade axle-build-tool   # occasionally
```

It requires `AXLE_API_KEY` in the environment. `axbt debug` is the first stop
whenever anything seems off: key acceptance, resolved environment, config,
and cache state in one shot.

## Project anatomy

`axbt init PATH` scaffolds the config plus a starter module. Config keys:
`project.name`, `project.minify` (payload minification, default on),
`modules.<Name>.dir` (module = directory of `.lean` files; `targets:` is
deprecated — `--select` is the narrowing mechanism), and
`axle.environment` / `timeout_seconds` / `global_options` (e.g.
`maxHeartbeats` for whnf-heavy proofs; scoped `set_option … in` also works
in plain Lean source). Pin the environment: submissions and stamp
signatures key on the resolved environment, so an unpinned project can
flip and invalidate the whole cache.

Writing Lean code: small single-purpose files; import siblings by file
stem (`import Basics`); imports are DAG-ordered by axbt. Files are the
unit of execution — a bare run judges every file, `--select` narrows.

## Disk artifacts — the debugging surface

Everything under `.axbt/` (gitignore it) is offline and free to inspect:

- `manifest.json` — rewritten by every compile; one node per file with
  `md5`/`status` (change detection), `parents`/`children` (the DAG),
  per-declaration `line_pos`/`end_line_pos` (source-accurate spans),
  `signature`, `dependencies`/`external_dependencies`, `is_sorry`, and
  outcome stamps (`checked_sig`/`checked_request_id`,
  `verified_sig`/`verified_*`/`verified_request_id`). Compact single-line
  JSON — pipe through `python -m json.tool`.
- `compiled/` — per-file payloads as of the last compile: exactly what a
  bare run would submit (minified by default; dependency sources inlined
  dependencies-first; imports hoisted into one header block). Rewritten
  per compile; GC prunes files whose sources no longer exist. `--sorry`
  runs also persist the `_stubbed.lean` variants actually sent. Scripted
  `--select` trim shapes and OK-run submissions are NOT here — only
  `failed/` carries exact per-selection content.
- `failed/` — one `<id>.lean` + `<id>.map.json` pair per FAIL (check or
  verify): the exact bytes the API saw, and the payload→source map
  (`sections`, per-section `line_map` → original file lines, `paths`,
  `tier`, `request_id`). Survives recompiles; request-id-keyed so retries
  accumulate side by side (`noid-…` stems when the API returns no id).
  OK/SKIP verdicts persist nothing.

## The iteration loop

1. **Edit** the Lean source.
2. **`axbt compile`** — MD5-diff, extract via the API (unchanged files
   make no API calls); prunes dead payloads (issue-style GC, prints what
   it pruned); regenerates `compiled/`.
3. **`axbt build`** — check pass streams first, then verify skips the
   selections whose check failed; rows tag `[check]`/`[verify]`;
   `--fail-fast` in the check pass abandons the build before verifying.
4. **`axbt check`** — fast typechecking, delta-cached: a file whose
   declarations all carry a `checked_sig` matching the current closure is
   `OK (cached)`; `--force` re-checks everything.
5. **`axbt verify`** — kernel-level verdict on finished proofs (rejects
   `sorry`, missing proofs, axiom-dependence). Per-declaration cache
   keyed on content + environment + options; `--force` re-verifies.
6. **`axbt list` / `axbt graph`** — offline orientation: the parsed
   declaration tree with `sorry` markers and file-accurate positions,
   or an interactive HTML DAG colored per declaration by stamp state.

## Debugging workflows

**Attribution first, artifacts second.** Failing rows print positions
rewritten to real source files, and attributable messages name the
covering declaration: `<file>:<line> … (declaration 'name')`. Fall
through to the disk artifacts only when positions are out-of-reach (the
unrewritten `-:N:N` form — header or out-of-range), when a
composition/shape question is involved, or when byte-level evidence is
needed.

**FAIL autopsy (usually all offline):**

1. Read the payload named on the FAIL line — `failed/<id>.lean` is the
   exact submitted content, the one shape the printed coordinates refer
   to. The lines map back through `<id>.map.json` (`line_map` per
   section; `sections` bounds each file's block; `paths` names files).
2. Correlate `request_id` against the manifest's stamps
   (`checked_request_id` / `verified_request_id`) to pin which
   re-judgment produced it, and node `md5`s to confirm the on-disk
   content the payload was built from.
3. Deterministic failures persist the same content each retry (a fresh
   request id per attempt): a minimal source tweak + re-run that still
   fails is a span bisector whose every attempt is preserved on disk.
4. Interrupted runs self-heal — a torn manifest fails validation and the
   next compile re-extracts from scratch; no stale verdicts serve.

**Composition questions** (what was / will be sent): read `compiled/` —
but remember it reflects the last compile, never unsaved editor state,
and never a trimmed `--select` shape.

**Cache forensics**: cached rows serve because the manifest carries
matching stamps; `--force` bypasses them narrowly. CAUTION:
`--no-compile` takes the manifest at face value — after edits prefer a
plain run, or `axbt compile --full-refresh` resets extraction state at
the cost of API calls on everything (it is the reliable unclog-everything
lever).

## Key semantics

- check compiles ≠ verified: a `sorry` typechecks (warning only); only
  verify certifies. A green check is never proof-completeness.
- `--select` (`<Module>` / `<Module.File>` / `<Module.File.decl>`,
  unique suffixes allowed) narrows without touching config; declaration
  selects must name a theorem/lemma — defs go through file/module
  selects.
- `--sorry <selector>` (repeatable) stubs theorem proof bodies in a
  dependency subtree — statements intact, so it is usable while upstream
  is unfinished. Def/abbrev bodies stay real (downstream proofs unfold
  them: anonymous constructors, projections, `rfl`). Granted selections
  report SKIP. On verify, granted stubs are named to the API's
  `permitted_sorries` and never recorded as verified.
- `--permitted-sorries <selector>` (verify only) excuses a genuinely
  sorried-in-source declaration without stubbing anything — use it when
  the target only needs the upstream's own `sorry` excused, and `--sorry`
  when you want complete-but-untrusted upstreams treated as axioms.
- Minification is on by default (comments, docstrings, blank lines
  stripped; attribution exact); `--no-minify` opts a run out and
  `project.minify: false` changes the default. Minify changes ride the
  stamp signature, so a flip re-judges exactly once.
- `--share` prints a web link to that exact run (check UI / verify UI);
  best effort, never affects exit codes.
- Concurrency is bounded (`AXLE_MAX_CONCURRENCY`, timeout via
  `axle.timeout_seconds`); interrupted runs are safe per above.

## Typical agent loop

- Scaffold: `axbt init my-proofs`, then edit `axbt_project.yml` and the
  module sources.
- Iterate: `axbt check --select <file>` → fix attributed errors →
  repeat; escalate to the FAIL-autopsy workflow when positions or report
  shapes run out.
- Authoritative finish line: `axbt build` (or a bare `axbt verify`)
  exiting 0. Before claiming success to the user, land on the verify
  tier — a green `check` is not sufficient on its own.
- Unfinished upstream while proving a new theorem:
  `axbt build --sorry <upstream-file>`, or `--permitted-sorries
  <selector>` when only that one declaration is sorried in source.
