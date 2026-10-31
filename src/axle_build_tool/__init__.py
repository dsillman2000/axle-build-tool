"""axbt (Axle Build Tool) — a dbt-inspired build tool for Lean 4 projects.

Executed via the Axle (Axiom Lean Engine) API. See GEMINI_PLAN.md for the
full specification.
"""

from axle_build_tool.cli import main

__all__ = ["main"]
