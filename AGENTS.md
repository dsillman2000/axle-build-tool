# axle-build-tool — Workspace Instructions

## Project overview

`axle-build-tool` (`axbt`) is a dbt-inspired build/orchestration tool for
Lean 4 projects, executed via the Axle (Axiom Lean Engine) API.

## Layout

- `src/axle_build_tool/` — package source (CLI entry point: `axbt = axle_build_tool:main`)
- `tests/` — pytest suite
- `demos/` — sample Lean 4 projects (e.g. `GaussIntSum`, `RootTwoIrrational`) used as end-to-end fixtures
- `pyproject.toml` — project metadata and dependencies (managed with `uv`)
- `GEMINI_PLAN.md` — planning notes

## Conventions

- Python >= 3.12; dependencies: `click`, `pydantic` (config validation via `axbt_project.yml`), `pyyaml`.
- Use `uv` for environment/dependency management (`uv sync`, `uv run`).
- Run tests with `uv run pytest` before considering work complete.
- Config validation is Pydantic-based — extend models rather than ad-hoc parsing.
- Keep the `axle-build-tool` script alias working alongside `axbt`.

## Git policy

- Default branch workflow: feature branches merged via pull requests (e.g. `opencode/phase-1-core-cli-config`).
- Write clear, imperative commit messages.
