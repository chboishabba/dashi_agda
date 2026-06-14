from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "uct_missing_math_theorem_agenda.py"
EXPECTED_IDS = [f"UCT-{letter}" for letter in "ABCDEFGH"]


def run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def load_agenda() -> dict[str, Any]:
    result = run_script()
    assert result.returncode == 0, result.stderr or result.stdout
    payload = json.loads(result.stdout)
    assert isinstance(payload, dict)
    return payload


def by_id(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = payload["theorem_targets"]
    return {row["id"]: row for row in rows}


def test_uct_agenda_emits_exact_fail_closed_ids_and_flags() -> None:
    payload = load_agenda()
    assert payload["ok"] is True
    assert payload["fail_closed"] is True
    assert payload["promotion_allowed"] is False
    assert payload["terminal_promotion"] is False

    rows = payload["theorem_targets"]
    assert [row["id"] for row in rows] == EXPECTED_IDS
    assert [row["title"] for row in rows] == [
        "OverlapResidualPDE",
        "EllipticityWitness",
        "CarlemanUniqueContinuation",
        "CrossTermNullity",
        "ModuloNullLinearity",
        "FourPointCancellation",
        "ParallelogramLaw",
        "JordanVonNeumannRecovery",
    ]
    for row in rows:
        assert row["promotion_allowed"] is False
        assert row["terminal_promotion"] is False
        assert row["theorem_statement"]
        assert row["symbolic_conclusion"]
        assert row["required_inputs"]


def test_uct_agenda_dependency_chain_and_downstream_locks() -> None:
    rows = by_id(load_agenda())
    assert rows["UCT-A"]["dependencies"] == []
    assert rows["UCT-B"]["dependencies"] == ["UCT-A"]
    assert rows["UCT-C"]["dependencies"] == ["UCT-A", "UCT-B"]
    assert rows["UCT-D"]["dependencies"] == ["UCT-A", "UCT-B", "UCT-C"]
    assert rows["UCT-E"]["dependencies"] == ["UCT-D"]
    assert rows["UCT-F"]["dependencies"] == ["UCT-D", "UCT-E"]
    assert rows["UCT-G"]["dependencies"] == ["UCT-D", "UCT-E", "UCT-F"]
    assert rows["UCT-H"]["dependencies"] == ["UCT-D", "UCT-G"]

    for theorem_id in ("UCT-E", "UCT-F", "UCT-G", "UCT-H"):
        assert rows[theorem_id]["status"] == "downstream-locked"
        assert "UCT-D" in rows[theorem_id]["dependencies"]

    assert rows["UCT-D"]["downstream_unlocks"] == ["UCT-E", "UCT-F", "UCT-G", "UCT-H"]


def test_uct_agenda_validates_current_evidence_markers() -> None:
    payload = load_agenda()
    markers = {
        marker
        for row in payload["theorem_targets"]
        for marker in row["evidence_markers"]
    }
    assert {
        "uct1ResidualPDESpecificationRecorded",
        "uct2EllipticityOrParabolicityClassRecorded",
        "uct3CarlemanUniqueContinuationRecorded",
        "uct4ActualTheoremTargetRecorded",
        "moduloNullLinearityConsumer",
        "fourPointConsumer",
        "parallelogramConsumer",
        "jordanVonNeumannAdapterConsumer",
    }.issubset(markers)


def test_uct_agenda_markdown_includes_theorem_ids() -> None:
    result = run_script("--format", "md")
    assert result.returncode == 0, result.stderr or result.stdout
    assert "# Paper 8 UCT Missing-Math Theorem Agenda" in result.stdout
    for theorem_id in EXPECTED_IDS:
        assert theorem_id in result.stdout
