# axle-build-tool — Workspace Instructions

## What this is

`axbt` is a dbt-inspired build/orchestration tool for Lean 4 projects,
executed through the Axle (Axiom Lean Engine) API. The authoritative
documentation is `README.md`; the GitHub issues carry the design
history.

## Layout

- `src/axle_build_tool/cli.py` — all commands (`init`/`compile`/`check`/`verify`/`list`/`debug`) and the report logic. Shared seams: `make_axle_service` (test injection), `_build_plan`, `_run_compile`.
- `src/axle_build_tool/axle_service.py` — the only place that talks to the API. Wraps the `axiom-axle` SDK (`AxleClient`); translates SDK errors into `AxleServiceError`.
- `src/axle_build_tool/manifest.py` — Pydantic manifest models (`ExtractedDecl` carries extraction data, dependency lists, and the check/verify stamp tiers).
- `src/axle_build_tool/payloads.py` — standalone payload assembly (deps inlined), line maps for message attribution.
- `src/axle_build_tool/stubbing.py` — `--sorry` span replacement; `bare_name` (canonical labels).
- `src/axle_build_tool/scopes.py` — Lean scope-header parser (`preamble_at` reconstructs scope context; currently uncalled — built for the parked declaration-cutting extension).
- `src/axle_build_tool/selection.py` — `--select` grammar: `module[.file-stem[.declaration]]` (greedy stem, unique-suffix decl match).
- `src/axle_build_tool/graph.py` — offline Cytoscape.js `graph.html` generation (outcome-stamp-keyed colors; the only external asset is a pinned CDN script). `--select`/closure reuse mirrors `axbt list`.
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
- **Manifest v2:** additive optional fields (e.g. `checked_request_id`) do not bump `version`; a version mismatch triggers a full self-healing re-extract. Stamps are written **only for declarations actually judged by a clean, fully unstubbed submission** — permitted, stubbed, cached, and failed ones are never stamped. The two tiers are separate facts on one `ExtractedDecl`: check stamps (`checked_sig`/`checked_at`/`checked_request_id`, written by `check`) and verification stamps (`verified_sig`/`verified_at`/`verified_request_id`, swept-only, so stubbed/permitted/cached never appear there). Neither tier consults the other's fields.
- **Check has no cache:** check re-submits every run and re-stamps; the two commands share the key material (`closure_signature` — file closure md5s + environment + global options) but a check cache would be behavior change territory and is parked.
- **Verify cache:** per-declaration stamps keyed on file-closure content + resolved environment + global options (selection-independent). A fully-cached selection skips submission (`OK (cached)`); `--force` re-verifies; `--share` may mint links for cached selections from the recorded request id.
- **Stubbing is local span replacement** from extraction spans/signatures (never a remote transform): `:= by sorry` for proof kinds only — def/abbrev grants keep their real bodies (definitional content downstream proofs unfold: anonymous constructors against the type, projections, `rfl`) while still counting as granted/excused, and structural kinds stay real entirely. Stale/overlapping spans are skipped with a warning prescribing `axbt compile`.
- **`--share` is stdout-only and best-effort**: one link per submission, keyed on `response.info["request_id"]`; a failed mint warns and never changes the exit code; sharing itself writes nothing to the manifest (the manifest changes an okay check/verify run makes are the outcome stamps, not share data). Minting goes through `AxleService.share_link` (raw POST to `/v1/shared-links` — outside the SDK's `api/v1` surface, answers 201, which the SDK's `_call` rejects).
- **Offline tests must stay offline:** no network, no `demos/` references. Live tests live in `tests/test_live.py` under `pytest -m live` and build their own projects.
- **Styled output:** green OK / red FAIL / dim metadata, white START, with click's tty detection handling piping. Every report line (START, verdicts, local answers, summaries) carries a `HH:MM:SS.mmm` timestamp, and submissions announce themselves dbt-style with a white START line + `[RUN]` suffix at actual dispatch under the same item-indexed `[n/m]` counter their verdicts print (never for locally-answered selections). Tests assert on whitespace-normalized lines via the conftest helpers — update those assertions when changing report shapes (see `_printed_lines`/`_decl_verdict` for the per-declaration report pattern).
- **Declaration-cutting payloads are parked** (per-decl payload isolation beyond current file-granularity). If revisiting, start from the design notes in the issue #12 close-out: manifest v3 dependency lists, attribute-span extension, scope-preamble assembly.

## Conventions

- Python >= 3.12; deps: `click`, `pydantic` (config validation via `axbt_project.yml` — extend models, never ad-hoc parse), `pyyaml`. Manage everything with `uv` (`uv sync`, `uv run`).
- Keep both the `axbt` and `axle-build-tool` script aliases working.
- New user-facing behavior needs: offline tests (fake-client driven), a live test when it touches the API's semantics, and README updates.
- Code/docstrings/comments must not reference planning documents or their section/phase numbering — write normal prose. (The planning docs were removed; the code, README, and issues carry the full context.)

## Git policy

- Feature branches prefixed `opencode/`, merged via PRs into `main` (CI gates: offline tests, live suite, per-demo pipelines — all unconditional).
- Imperative commit messages. **Never use backticks inside `git commit -m`** — zsh command substitution; write the message to a file and use `git commit -F <file>`.
- Small user-requested fixes may land directly on `main` when the user asks for it.

## Agent conventions

- **Branch prefix:** agent-driven development branches are always prefixed `opencode/` (e.g. `opencode/manifest-outcome-records`) and land via PRs into `main` (see Git policy).
- **Sign-off:** agent-authored GitHub artifacts *saved outside the commit itself* — namely PR descriptions, issue bodies, and comments on PRs/issues — end with a horizontal rule and an italicized sign-off, exactly:

  ```
  ---
  *Written by OpenCode.*
  ```

  Ordinary chat replies and commit messages are not signed; only those three artifact kinds.
