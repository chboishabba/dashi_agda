from __future__ import annotations

import json
import math
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "downloaded_ym_hodge_artifact_summary.py"
SOURCE_DIR = REPO_ROOT / "temp-DOWNLOADED" / "new additions"

EXPECTED_Q = 0.23178189475262734
HEX64 = re.compile(r"^[0-9a-f]{64}$")


def _run_summary_cli(tmp_path: Path) -> tuple[dict[str, Any], str]:
    if not SOURCE_DIR.exists():
        pytest.skip(f"downloaded additions directory is absent: {SOURCE_DIR}")
    if not SCRIPT.exists():
        pytest.skip(f"YM/Hodge artifact summary CLI is absent: {SCRIPT}")

    output_dir = tmp_path / "ym_hodge_summary"
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--source-dir",
            str(SOURCE_DIR),
            "--output-dir",
            str(output_dir),
            "--generated-at",
            "2026-06-07T00:00:00+00:00",
        ],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert result.returncode == 0, result.stderr or result.stdout

    json_outputs = sorted(output_dir.glob("*.json"))
    markdown_outputs = sorted(output_dir.glob("*.md"))
    assert json_outputs, "CLI should emit at least one JSON summary"
    assert markdown_outputs, "CLI should emit at least one Markdown report"

    summary = json.loads(json_outputs[0].read_text(encoding="utf-8"))
    markdown = markdown_outputs[0].read_text(encoding="utf-8")
    assert markdown.strip()
    return summary, markdown


def _walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for item in value.values():
            yield from _walk(item)
    elif isinstance(value, list):
        for item in value:
            yield from _walk(item)


def _find_key(value: Any, key: str) -> list[Any]:
    found: list[Any] = []
    for item in _walk(value):
        if isinstance(item, dict) and key in item:
            found.append(item[key])
    return found


def _first_number(summary: dict[str, Any], *keys: str) -> float | None:
    for key in keys:
        for value in _find_key(summary, key):
            if isinstance(value, int | float):
                return float(value)
    return None


def _all_named_flags(summary: dict[str, Any]) -> dict[str, bool]:
    flags: dict[str, bool] = {}
    for item in _walk(summary):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            lowered = key.lower()
            if isinstance(value, bool) and (
                "promot" in lowered or "clay_yang_mills" in lowered
            ):
                flags[key] = value
    return flags


def _checksum_values(summary: dict[str, Any]) -> list[str]:
    checksums: list[str] = []
    for item in _walk(summary):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            lowered = key.lower()
            if "sha256" in lowered or "checksum" in lowered:
                if isinstance(value, str) and HEX64.fullmatch(value):
                    checksums.append(value)
    return sorted(set(checksums))


def test_downloaded_ym_hodge_summary_cli_emits_json_and_markdown(tmp_path: Path):
    summary, markdown = _run_summary_cli(tmp_path)

    assert isinstance(summary, dict)
    assert "hodge" in json.dumps(summary, sort_keys=True).lower()
    assert "ym" in json.dumps(summary, sort_keys=True).lower() or "yang" in (
        json.dumps(summary, sort_keys=True).lower()
    )
    assert "hodge" in markdown.lower()
    assert "ym" in markdown.lower() or "yang" in markdown.lower()


def test_downloaded_ym_hodge_summary_pins_wc3_arithmetic_boundary(tmp_path: Path):
    summary, _markdown = _run_summary_cli(tmp_path)

    q = _first_number(summary, "q", "Q_CURRENT", "q_current")
    if q is not None:
        assert math.isclose(q, EXPECTED_Q, rel_tol=0.0, abs_tol=1e-15)

    eta4_q = _first_number(summary, "eta4_q")
    eta8_q = _first_number(summary, "eta8_q")
    su3_first_safe_k = _first_number(summary, "su3_first_safe_k")

    assert eta4_q is not None
    assert eta8_q is not None
    assert su3_first_safe_k is not None
    assert eta4_q < 1
    assert eta8_q > 1
    assert int(su3_first_safe_k) == 11

    route_decisions = [str(value) for value in _find_key(summary, "route_decision")]
    assert route_decisions, "summary should expose a route_decision"
    assert any("MASTER_WC3" in decision for decision in route_decisions)


def test_downloaded_ym_hodge_summary_keeps_promotion_false(tmp_path: Path):
    summary, _markdown = _run_summary_cli(tmp_path)

    flags = _all_named_flags(summary)
    assert flags, "summary should expose explicit promotion flags"
    assert all(value is False for value in flags.values()), flags


def test_downloaded_ym_hodge_summary_binds_source_artifact_checksums(
    tmp_path: Path,
):
    summary, _markdown = _run_summary_cli(tmp_path)

    checksums = _checksum_values(summary)
    assert len(checksums) >= 8
