# axbt (Axle Build Tool) — MVP Requirements & Architecture Specification

This document outlines the core architecture, functional requirements, and developer workflow for **`axbt`** (Axle Build Tool), a dbt-inspired build and orchestration tool designed for Lean 4 projects executed via the **Axle** (Axiom Lean Engine) SDK/CLI.

---

## 1. Executive Summary & Vision

Formal theorem proving in Lean 4 often forces a compromise between monolithic files (which are slow to check and difficult to isolate) and modular files (which require fragile, manual import chains and strict scope management).

**`axbt`** bridges this gap by applying the proven data-pipeline concepts of **dbt (data build tool)** to formal verification:

* **Lean Models:** Modular `.lean` files or distinct declaration blocks treated as isolated verification targets ("models").
* **Dependency Graphs (DAG):** Automatic parsing of standard Lean `import` statements to construct project lineage and track metadata via `manifest.json`.
* **Incremental Builds:** MD5 fingerprinting to avoid redundant extraction and verification of unchanged files.
* **Rapid Feedback Tiers:** Separation of lightweight typechecking (`axbt check`) from rigorous proof verification (`axbt verify`).

---

## 2. Project Structure & Configuration (`axbt_project.yml`)

The project root will contain a central configuration file, `axbt_project.yml`, which defines project metadata, source directories, and target output paths.

```yaml
project:
  name: "my_lean_project"
  version: "0.1.0"

dirs:
  models: "models"
  target: "target"
  cache: ".axbt"

axle:
  endpoint: "local" # or remote axle connection details

```

### Directory Layout

```text
my_lean_project/
├── axbt_project.yml
├── models/
│   ├── base/
│   │   └── numbers.lean
│   └── derived/
│       └── arithmetic.lean
└── .axbt/
    ├── manifest.json            # Full project DAG and metadata
    ├── cache/
    │   ├── numbers.md5          # MD5 hash for change detection
    │   └── arithmetic.md5
    └── compiled/
        ├── numbers_isolated.lean  # Cached isolated verification targets
        └── arithmetic_isolated.lean

```

---

## 3. Incremental Caching & State Management

To ensure fast execution cycles, `axbt` maintains a local cache (`.axbt/`) that tracks file states:

* **MD5 Fingerprinting:** During `axbt compile`, the tool computes an MD5 hash for each source file in `models/`.
* **Change Detection:** If a file's hash matches its cached `.md5` counterpart, downstream extraction and compilation steps are skipped.
* **Inspection Support:** All generated, isolated, and stubbed source files are preserved in `.axbt/compiled/`, allowing developers to inspect the exact payload sent to Axle when debugging verification failures.

---

## 4. Manifest & DAG Engine (`manifest.json`)

`axbt` parses standard Lean `import` statements to map dependencies between models, compiling them into a structured Directed Acyclic Graph (DAG) exported to `target/manifest.json`.

* **Declaration Extraction:** Interacts with Axle's underlying native metadata APIs (`extract_decls`) to catalog declarations, types, and dependencies without requiring a heavy local Lean compiler installation.
* **Node Metadata:** Each entry in `manifest.json` tracks:
* Unique model identifier / name
* Source file path
* Direct upstream dependencies (parents)
* Downstream dependents (children)
* Current compilation/verification status and last-checked timestamp



---

## 5. Isolation, Stubbing & Scope Management

Checking a single model in isolation requires reconstructing its required context while stubbing out unneeded code:

* **Upstream `sorry`-ing:** When executing an isolated model, upstream dependencies are automatically stubbed out with `sorry` or axiom placeholders to isolate the proof/definition under test.
* **Scoping Preservation:** Special care is taken to wrap extracted code blocks in their respective `namespace`, `section`, `variable`, and `open` headers to prevent name-resolution or scope errors.

---

## 6. CLI Command Architecture

The `axbt` CLI supports three primary commands mirroring a progressive developer workflow:

| Command | Description | Performance & Purpose |
| --- | --- | --- |
| **`axbt compile`** | Scans `models/`, checks MD5 hashes, updates the DAG, and outputs `target/manifest.json`. | **Fast:** Only re-extracts declarations for modified files. |
| **`axbt check`** | Assembles the isolated model (with upstream `sorry` stubs) and submits it for a rapid typecheck via Axle. | **Fast & Lightweight:** Optimized for daily modeling and rapid proof iteration. |
| **`axbt verify`** | Executes rigorous kernel-level proof verification or equality checking via Axle. | **Slow & Strict:** Intended for final validation, release gates, and CI/CD pipelines. |

---

## 7. MVP Implementation Roadmap

1. **Phase 1 (Core CLI & Config):** Implement `axbt_project.yml` parsing, directory initialization (`axbt init`), and file-system scanning.
2. **Phase 2 (Parser & DAG):** Integrate standard Lean import parsing, MD5 caching, and `manifest.json` generation.
3. **Phase 3 (Axle Integration):** Connect `axbt compile` and `axbt check` to the Axle SDK/CLI endpoints for declaration extraction and lightweight checking.
4. **Phase 4 (Isolation Engine):** Build the automated stubbing mechanism to handle namespaces, sections, and upstream `sorry` injection for isolated model execution.
