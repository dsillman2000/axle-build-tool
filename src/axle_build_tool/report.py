"""Shared report-formatting helpers for the streaming CLI report.

One formatting authority for the report's clock, item counter, and
timing text — every command's streaming lines (extractions, checks,
verifies, builds) print dbt-style rows with the same shapes.
"""

from __future__ import annotations

from datetime import datetime


def timing_text(seconds: float) -> str:
    """A measured duration formatted for the report, e.g. `1.234s`."""
    return f"{seconds:.3f}s"


def clock() -> str:
    """The report timestamp: local `HH:MM:SS.mmm`, fixed width so every
    report line's columns align."""
    return datetime.now().strftime("%H:%M:%S.%f")[:-3]


def item_counter(position: int, total: int) -> str:
    """The dbt-style item counter `[ 3/25]`, padded for alignment.

    Indexed by planned position, not by completion order: a submission
    announces itself (START) and reports its verdicts under the same
    counter, dbt pairing, however the completions interleave.
    """
    width = max(len(str(total)), 1)
    return f"[{position:>{width}}/{total}]"
