"""CLI-level SDK-error mapping (Scope F / acceptance criterion 14).

Every SDK exception family must surface through each submission
command as a distinct, friendly, actionable one-liner — with exit 1 —
rather than a traceback. The service layer's mapping is unit-tested in
`test_axle_service.py`; this file drives the real CLI so the messages
are asserted in command output.
"""

from __future__ import annotations

import os
from pathlib import Path

import pytest
from axle.exceptions import (
    AxleApiError,
    AxleForbiddenError,
    AxleInvalidArgument,
    AxleIsUnavailable,
    AxleRateLimitedError,
    LeanResourceExceeded,
    LeanTimeout,
)
from click.testing import CliRunner

from axle_build_tool import main
from conftest import make_document

runner = CliRunner()

TARGETS_CONFIG = """\
project:
  name: proj
modules:
  M:
    targets:
      - A.t1
"""

FILES = {"M/A.lean": "theorem t1 : 1 = 1 := rfl\n"}

DOCS = {
    "theorem t1 : 1 = 1": {
        "t1": make_document("t1", kind="theorem", line_pos=1, end_line_pos=1)
    }
}

#: (SDK exception, a fragment of its friendly message that must appear
#: in the command's output).
ERROR_CASES = [
    (AxleIsUnavailable("https://axle.axiommath.ai", "connection refused"), "unreachable"),
    (AxleForbiddenError("403"), "AXLE_API_KEY"),
    (AxleRateLimitedError("429"), "rate limit"),
    (LeanTimeout("timed out"), "axle.timeout_seconds"),
    (LeanResourceExceeded("heartbeats"), "global_options"),
    (AxleInvalidArgument("bad request"), "invalid"),
    (AxleApiError("500"), "Axle API error"),
]


def prepare(make_project, tmp_path: Path, monkeypatch, fake_axle) -> Path:
    """A compiled project, ready for the test to arm the fake's error."""
    root = make_project(tmp_path, TARGETS_CONFIG, FILES)
    monkeypatch.chdir(root)
    fake_axle._extract_documents_by_marker = DOCS
    assert runner.invoke(main, ["compile"]).exit_code == 0
    fake_axle.calls.clear()
    return root


@pytest.mark.parametrize(("exc", "fragment"), ERROR_CASES)
class TestSdkErrorMapping:
    def test_check_maps_sdk_errors_to_friendly_messages(
        self, exc, fragment, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = prepare(make_project, tmp_path, monkeypatch, fake_axle)
        fake_axle._error = exc

        result = runner.invoke(main, ["check", "--no-compile"])

        assert result.exit_code == 1
        assert fragment in result.output
        # The error names the selection it concerns.
        assert "M.A.t1" in result.output

    def test_verify_maps_sdk_errors_to_friendly_messages(
        self, exc, fragment, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = prepare(make_project, tmp_path, monkeypatch, fake_axle)
        fake_axle._error = exc

        result = runner.invoke(main, ["verify", "--no-compile"])

        assert result.exit_code == 1
        assert fragment in result.output
        assert "M.A.t1" in result.output

    def test_compile_maps_sdk_errors_to_friendly_messages(
        self, exc, fragment, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = prepare(make_project, tmp_path, monkeypatch, fake_axle)
        fake_axle._error = exc

        result = runner.invoke(main, ["compile", "--full-refresh"])

        assert result.exit_code == 1
        assert fragment in result.output

    def test_bare_check_maps_sdk_errors_from_the_precursor(
        self, exc, fragment, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        """A default check surfaces precursor-compile API failures too."""
        root = prepare(make_project, tmp_path, monkeypatch, fake_axle)
        # Touch the file so the precursor has extraction to do (the
        # fake errors on every call, including auto-environment probes).
        fake_axle._error = exc
        (root / "M/A.lean").write_text(
            "theorem t1 : 1 = 1 := rfl\ntheorem extra : 2 = 2 := rfl\n",
            encoding="utf-8",
        )

        result = runner.invoke(main, ["check"])

        assert result.exit_code == 1
        assert fragment in result.output


@pytest.mark.skipif(
    hasattr(os, "geteuid") and os.geteuid() == 0,
    reason="root can read files regardless of permissions",
)
class TestUnreadableSources:
    """An unreadable source is a friendly error, not a traceback."""

    def test_check_reports_unreadable_source(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = prepare(make_project, tmp_path, monkeypatch, fake_axle)
        (root / "M/A.lean").chmod(0o000)

        result = runner.invoke(main, ["check", "--no-compile"])

        assert result.exit_code == 1
        assert "Error:" in result.output
        assert "M/A.lean" in result.output

    def test_verify_reports_unreadable_source(
        self, make_project, tmp_path: Path, monkeypatch, fake_axle
    ) -> None:
        root = prepare(make_project, tmp_path, monkeypatch, fake_axle)
        (root / "M/A.lean").chmod(0o000)

        result = runner.invoke(main, ["verify", "--no-compile"])

        assert result.exit_code == 1
        assert "Error:" in result.output
        assert "M/A.lean" in result.output
