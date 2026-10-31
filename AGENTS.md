# axle-build-tool — Workspace Instructions

## What this is

`axbt` is a dbt-inspired build/orchestration tool for Lean 4 projects,
executed through the Axle (Axiom Lean Engine) API. The authoritative
spec is `GEMINI_PLAN.md` (§6 = command architecture, §7 = demos).

## Layout

- `src/axle_build_tool/cli.py` — all commands (`init`/`compile`/`check`/`verify`/`list`/`debug`) and the report logic. Shared seams: `make_axle_service` (test injection), `_build_plan`, `_run_compile`.
- `src/axle_build_tool/axle_service.py` — the only place that talks to the API. Wraps the `axiom-axle` SDK (`AxleClient`); translates SDK errors into `AxleServiceError`.
- `src/axle_build_tool/manifest.py` — Pydantic manifest models (`ExtractedDecl` carries extraction data + verification stamps).
- `src/axle_build_tool/payloads.py` — standalone payload assembly (deps inlined), line maps for message attribution.
- `src/axle_build_tool/stubbing.py` — `--sorry` span replacement; `bare_name` (canonical labels).
- `src/axle_build_tool/scopes.py` — Lean scope-header parser (`preamble_at` reconstructs scope context; currently uncalled — built for the parked declaration-cutting extension).
- `src/axle_build_tool/selection.py` — `--select` grammar: `module[.file-stem[.declaration]]` (greedy stem, unique-suffix decl match).
- `tests/` — pytest suite; `tests/conftest.py` has `FakeAxleClient` (the offline API fake) and assertion helpers (`status_line`, `normalized_lines`).
- `demos/small/` — integration-only demo projects (`RootTwoIrrational`, `GaussIntSum`); exercised by `.github/workflows/demo.yml`.

## Commands

- `uv sync` — set up the environment (fnm users: `eval "$(fnm env --use-on-cd)"` first).
- `uv run pytest` — the offline suite; **must be green before any work is "done"**. Don't chain follow-up commands onto a piped pytest (`| tail` masks the exit code).
- `AXLE_API_KEY=... uv run pytest -m live` — live suite against the real API (self-contained ad-hoc projects; never demos). CI runs it unconditionally on every PR.
- Demo pipeline: `cd demos/small/<demo>` then `uv run axbt compile && axbt check && axbt verify` — plain `uv run` works there because uv walks up to the repo `pyproject.toml`.

## Architecture invariants

- **All proof work goes through the axle SDK — never a local `lean` binary.** The CLI is synchronous and bridges into the async service via `asyncio.run`; concurrency is bounded by a semaphore (`max_concurrency`).
- **Two judging tiers, do not conflate:** `check` = typecheck (a `sorry` elaborates with a warning and does *not* fail it); `verify` = kernel-level (sorries and axiom-dependence fail unless excused by `--permitted-sorries`). The verify sweep certifies the whole payload closure; check's focused mode (`names=[decl]`) makes the API's per-decl "incomplete" signal unreliable (it internally sorries dependencies), so statuses key on `response.okay`.
- **Manifest v2:** additive optional fields (e.g. `verified_request_id`) do not bump `version`; a version mismatch triggers a full self-healing re-extract. Verification stamps (`verified_sig`/`verified_at`/`verified_request_id`) are written **only for declarations actually swept** — stubbed, permitted, and cached ones are never stamped.
- **Verify cache:** per-declaration stamps keyed on file-closure content + resolved environment + global options (selection-independent). A fully-cached selection skips submission (`OK (cached)`); `--force` re-verifies; `--share` may mint links for cached selections from the recorded request id.
- **Stubbing is local span replacement** from extraction spans/signatures (never a remote transform): `:= by sorry` for proof kinds, `:= sorry` for defs/abbrevs, structural kinds stay real. Stale/overlapping spans are skipped with a warning prescribing `axbt compile`.
- **`--share` is stdout-only and best-effort**: one link per submission, keyed on `response.info["request_id"]`; a failed mint warns and never changes the exit code; nothing is written to the manifest. Minting goes through `AxleService.share_link` (raw POST to `/v1/shared-links` — outside the SDK's `api/v1` surface, answers 201, which the SDK's `_call` rejects).
- **Offline tests must stay offline:** no network, no `demos/` references. Live tests live in `tests/test_live.py` under `pytest -m live` and build their own projects.
- **Styled output:** green OK / red FAIL / dim metadata, with click's tty detection handling piping. Tests assert on whitespace-normalized lines via the conftest helpers — update those assertions when changing report shapes (see `_printed_lines`/`_decl_verdict` for the per-declaration report pattern).
- **Declaration-cutting payloads are parked** (per-decl payload isolation beyond current file-granularity). If revisiting, start from the design notes in the issue #12 close-out: manifest v3 dependency lists, attribute-span extension, scope-preamble assembly.

## Conventions

- Python >= 3.12; deps: `click`, `pydantic` (config validation via `axbt_project.yml` — extend models, never ad-hoc parse), `pyyaml`. Manage everything with `uv` (`uv sync`, `uv run`).
- Keep both the `axbt` and `axle-build-tool` script aliases working.
- New user-facing behavior needs: offline tests (fake-client driven), a live test when it touches the API's semantics, and README + `GEMINI_PLAN.md` §6 updates.
- Code/docstrings/comments must not reference planning documents' section/phase numbering — write normal prose.

## Git policy

- Feature branches prefixed `opencode/`, merged via PRs into `main` (CI gates: offline tests, live suite, per-demo pipelines — all unconditional).
- Imperative commit messages. **Never use backticks inside `git commit -m`** — zsh command substitution; write the message to a file and use `git commit -F <file>`.
- Small user-requested fixes may land directly on `main` when the user asks for it.
