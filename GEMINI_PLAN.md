# axbt (Axle Build Tool) — MVP Requirements & Architecture Specification

This document outlines the core architecture, functional requirements, and developer workflow for **`axbt`** (Axle Build Tool), a dbt-inspired build and orchestration tool designed for Lean 4 projects executed via the **Axle** (Axiom Lean Engine) SDK/CLI.

---

## 1. Executive Summary & Vision

Formal theorem proving in Lean 4 often forces a compromise between monolithic files (which are slow to check and difficult to isolate) and modular files (which require fragile, manual import chains and strict scope management).

**`axbt`** bridges this gap by applying the proven data-pipeline concepts of **dbt (data build tool)** to formal verification:

* **Modules:** Named directories of `.lean` files (the dbt "model" analog) whose declarations are addressed as isolated verification **targets**.
* **Dependency Graphs (DAG):** Automatic parsing of standard Lean `import` statements to construct project lineage and track metadata via `manifest.json`.
* **Incremental Builds:** MD5 fingerprinting to avoid redundant extraction and verification of unchanged files.
* **Rapid Feedback Tiers:** Separation of lightweight typechecking (`axbt check`) from rigorous proof verification (`axbt verify`).

---

## 2. Project Structure & Configuration (`axbt_project.yml`)

The project root will contain a central configuration file, `axbt_project.yml`, which defines project metadata, the project's modules, and Axle API settings. YAML serde (parsing `axbt_project.yml`, and writing it during `axbt init` scaffolding) uses the [**`PyYAML`**](https://pyyaml.org/) Python library.

```yaml
project:
  name: "my_lean_project"
  version: "0.1.0"

modules:
  RootTwoIrrational: # module name; used as the first component of selectors
    dir: "RootTwoIrrational" # optional; defaults to the module name
    targets: # default build set for a bare `axbt check`
      - Divisibility.prime_gt_one
      - Divisibility.prime_dvd_square
      - EuclidLemma.euclid_lemma

axle:
  environment: "lean-4.35.0" # Lean environment for the Axle API
  timeout_seconds: 120 # Per-request timeout for Axle API calls
  global_options: # Lean global options passed through to Axle
    maxHeartbeats: 100000
```

`modules` is a mapping of module names to module configs. Each entry describes one module — a named directory of `.lean` files:

* **`dir`:** Path of the module's source directory, relative to the project root. Optional; defaults to the module's name.
* **`targets`:** Module-relative selectors (`<file>.<declaration>`) for the isolated theorems/lemmas that form the module's **default build set**. A bare `axbt check` checks every target of every module; any other declaration can still be addressed ad hoc with `--select` (see §6). Note: declaration-level targets must be theorems/lemmas — Axle's name-focused checking does not resolve `def`s by name (see §6).

The `axle` section configures how `axbt` talks to the Axle (Axiom Lean Engine) API:

* **`environment`:** The Lean environment (toolchain version) Axle should run code in, e.g. `lean-4.35.0`.
* **`timeout_seconds`:** Maximum wall-clock time in seconds allowed for a single Axle request before it is cancelled.
* **`global_options`:** A dict of Lean global options applied to every submission (e.g. `maxHeartbeats`), forwarded verbatim to the API.

Notes on configuration behavior:

* **Cache directory:** `.axbt/` is the default and only cache location. It is **not** a configurable setting and cannot be overridden.
* **Connectivity:** `axbt` always executes against the remote Axle API configuration; there is no `endpoint` setting. Unit tests use mocks in place of the real API. All communication with the Axle API goes through the official Python SDK, [`axiom-axle`](https://pypi.org/project/axiom-axle/) (built on `aiohttp`, `requests`, and `tenacity`), rather than a raw HTTP client — the SDK's client, retry, and error-handling patterns should be used natively.

Authentication is handled via the **`AXLE_API_KEY`** environment variable, which is the default API key used for all `axbt` executions against the Axle API.

### Directory Layout

```text
my_lean_project/
├── axbt_project.yml
├── RootTwoIrrational/           # modules.RootTwoIrrational.dir
│   ├── Divisibility.lean
│   └── EuclidLemma.lean
└── .axbt/
    ├── manifest.json            # Full project DAG, metadata, and per-file MD5 hashes
    └── compiled/                # Cached standalone payloads (one per selection)
        ├── Divisibility_isolated.lean
        └── EuclidLemma_isolated.lean
```

---

## 3. Incremental Caching & State Management

To ensure fast execution cycles, `axbt` maintains a local cache (`.axbt/`) that tracks file states:

* **MD5 Fingerprinting:** During `axbt compile`, the tool computes an MD5 hash for each source file in every configured module directory and records it directly in `manifest.json` (as an `md5` field on each DAG node).
* **Change Detection:** If a file's current hash matches the `md5` recorded in `manifest.json`, downstream extraction and compilation steps are skipped.
* **Inspection Support:** All generated, isolated, and stubbed source files are preserved in `.axbt/compiled/`, allowing developers to inspect the exact payload sent to Axle when debugging verification failures.

---

## 4. Manifest & DAG Engine (`manifest.json`)

`axbt` parses standard Lean `import` statements to map dependencies between files across the configured modules, compiling them into a structured Directed Acyclic Graph (DAG) exported to `.axbt/manifest.json`.

* **Declaration Extraction:** Interacts with Axle's underlying native metadata APIs (`extract_decls`) to catalog declarations, types, and dependencies without requiring a heavy local Lean compiler installation.
* **Node Metadata:** Each entry in `manifest.json` tracks:
* Unique model identifier / name
* Source file path
* Direct upstream dependencies (parents)
* Downstream dependents (children)
* Current MD5 fingerprint of the source file (for incremental change detection)
* Current compilation/verification status and last-checked timestamp



---

## 5. Isolation, Stubbing & Scope Management

Checking a single model in isolation requires reconstructing its required context while stubbing out unneeded code:

* **Payload construction:** A selected model is compiled into a standalone `.lean` file by topologically flattening its dependency subgraph. By default the payload inlines the **full transitive source** of all upstream dependencies.
* **Opt-in stubbing (`--sorry`):** Passing `--sorry <selector>` replaces the proof bodies of the selected dependency subtree with `sorry` stubs (signatures preserved), trading completeness for speed when iterating against broken or slow-to-elaborate upstream code. The flag may be repeated to stub multiple subtrees.
* **Scoping Preservation:** Special care is taken to wrap extracted code blocks in their respective `namespace`, `section`, `variable`, and `open` headers to prevent name-resolution or scope errors.

---

## 6. CLI Command Architecture

The `axbt` CLI supports a progressive developer workflow. Command-line mechanics (argument parsing, subcommands, options like `--select`/`--sorry`, help output, exit codes) are implemented with the [**`click`**](https://click.palletsprojects.com/) Python library:

| Command | Description | Performance & Purpose |
| --- | --- | --- |
| **`axbt compile`** | Scans every configured module directory, checks MD5 hashes, updates the DAG, outputs `.axbt/manifest.json`, and (re)generates cached standalone payloads for all declared `targets`. Two run modes: `--incremental` (default) only re-extracts declarations for modified files; `--full-refresh` ignores the previous manifest and re-extracts everything. | **Fast:** Only re-extracts declarations for modified files (incremental mode). |
| **`axbt check`** | Runs `compile` first (unless `--no-compile` is passed, which takes the existing manifest at face value), assembles the standalone payload for the selection (inlining dependencies, stubbing only where `--sorry` requests it) and submits it for a rapid typecheck via Axle. The same run modes apply to the precursor; the check step always re-submits its selection. | **Fast & Lightweight:** Optimized for daily modeling and rapid proof iteration; the precursor compile is incremental (a clean tree makes no API calls). |
| **`axbt verify`** | Runs `compile` first (same run modes as `check`), then kernel-level verification: for each selection the payload's theorem proofs are stripped into a formal statement (the API's `theorem2sorry` transform, preserving imports and local definitions), and the real content is checked against it via `verify_proof`. Declaration-level selections focus on their own declaration (the payload's other theorems are `permitted_sorries`); selections carrying a `sorry` fail locally without an API call. | **Slow & Strict:** Intended for final validation, release gates, and CI/CD pipelines. |

Both judging commands accept `--share`: after the run, each submission's response (which carries a `request_id`) is registered with the API's share service, and a web link to that exact run prints under the selection's block — `share: <url>` — with the count in the summary. Sharing is best-effort: a failed mint prints a warning and never changes the exit code, and nothing is written to the manifest. `verify --share` also mints links for cached selections, referencing their most recent recorded verification (marked "(from the earlier run)").
| **`axbt list`** | Prints the parsed declaration tree (kinds, file-accurate positions, `sorry` markers) in topological order — dependencies first — offline and read-only, with `--select` filtering. | **Instant:** Inspection and orientation; no API calls. |
| **`axbt debug`** | Developer diagnostic: verifies `AXLE_API_KEY` is set and accepted by the API (masked echo, reachability with latency, resolved environment), and prints the project's configuration and `.axbt/` cache state. Exits 1 when the key fails. | **Diagnostic:** First stop when the environment or cache seems off. |

### Selection (`--select`) and stubbing (`--sorry`)

Selectors are dot-separated and resolved against the manifest: the first segment must match a module name, the next greedily matches a file stem, and the remainder — which may itself contain dots, since Lean declaration names do — is matched against the extracted declaration names.

Declaration-level selectors resolve against any extracted declaration, but **targeted (declaration-level) checks only work for theorems and lemmas**: Axle's name-focused checking resolves theorems by name only, so selecting a `def` fails at submission with `Theorem '<name>' not found` (observed live against the API). To check definitions, select the enclosing file or module instead.

| Invocation | Scope |
| --- | --- |
| `axbt check --select RootTwoIrrational` | Whole module: every file in the module, including dependencies, all flattened and checked. |
| `axbt check --select RootTwoIrrational.Divisibility` | Whole `Divisibility.lean` file, including dependencies. |
| `axbt check --select RootTwoIrrational.Divisibility.prime_dvd_square` | Single theorem, including its dependency subgraph. |

Without `--select`, every `targets` entry of every module is built. Standalone payloads inline the full transitive source of dependencies by default; `--sorry <selector>` swaps the selected dependency subtree for `sorry` stubs instead, e.g.

```text
axbt check --select RootTwoIrrational.EuclidLemma --sorry RootTwoIrrational.Divisibility
# checks EuclidLemma.lean, sorrying anything imported from Divisibility.lean
```

---

## 7. Demo Projects (`demos/small/`)

To validate end-to-end behavior, the repository includes small, self-contained demo projects under `demos/small/` (future demos that are large by contrast will live in sibling directories, e.g. `demos/large/`). Each demo is a complete, runnable `axbt` project (own `axbt_project.yml`, module source directory, and generated `.axbt/` output) and doubles as a regression fixture asserting that axbt's features work as expected.

### 7.1 `demos/small/RootTwoIrrational`

A project proving that `√2` is not rational (irrationality of the square root of two).

* **Module structure:** `Divisibility.lean` (helper lemmas such as `prime_gt_one` and `prime_dvd_square`), `EuclidLemma.lean` (`euclid_lemma`), and `IrrationalSqrtTwo.lean` (the main `sqrt_two_irrational` theorem: if `a * a = 2 * (b * b)` with `b ≠ 0`, then `2 ∣ a`, `b < a`, and strong induction on `a` closes the descent) — deliberately multi-file to exercise the import-DAG. Configured via the `modules`/`targets` example in §2.
* **Features exercised:** `axbt init` scaffolding, import parsing, all three `--select` granularities, `--sorry` stubbing, and the `axbt check` / `axbt verify` success paths.

### 7.2 `demos/small/GaussIntSum`

A project proving the Gauss summation identity: `1 + 2 + ⋯ + n = n * (n + 1) / 2` for the first `n` positive integers.

* **Module structure:** One file stating the identity (with the induction proof), possibly plus a small helper file for summation lemmas, imported via the DAG.
* **Features exercised:** incremental rebuild — after a scripted edit to a source file, `axbt compile` must re-extract *only* the modified file (MD5 change detection), plus declaration extraction and inspection of cached payloads in `.axbt/compiled/`.

### 7.3 Role as test cases

Both demos serve as executable acceptance tests for the tool:

* Running `axbt compile && axbt check` (including `--select`/`--sorry` combinations, and `axbt verify` where a full proof is present) inside each demo directory must succeed with zero errors.
* The `RootTwoIrrational` demo primarily validates correctness of DAG construction and stubbing; `GaussIntSum` primarily validates incremental caching behavior.
* They are kept out of the `axbt` package itself and exist purely as fixtures for integration tests and manual smoke-testing.

---

## 8. MVP Implementation Roadmap

1. **Phase 1 (Core CLI & Config):** Implement `axbt_project.yml` parsing (via `PyYAML`), directory initialization (`axbt init`), and file-system scanning, using the `click` library for command-line mechanics.
2. **Phase 2 (Parser & DAG):** Integrate standard Lean import parsing, MD5 caching, and `manifest.json` generation.
3. **Phase 3 (Axle Integration):** Connect `axbt compile` and `axbt check` to the Axle SDK/CLI endpoints for declaration extraction and lightweight checking, using the official [`axiom-axle`](https://pypi.org/project/axiom-axle/) Python SDK (not a raw HTTP client such as `httpx`) for all Axle API interactions.
4. **Phase 4 (Isolation Engine):** Build the automated stubbing mechanism to handle namespaces, sections, and upstream `sorry` injection for isolated model execution.
5. **Phase 5 (Demo Projects):** Create the `demos/small/RootTwoIrrational` and `demos/small/GaussIntSum` projects and wire them into the integration test suite as end-to-end acceptance fixtures.
