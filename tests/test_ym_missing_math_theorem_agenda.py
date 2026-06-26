from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_missing_math_theorem_agenda.py"
EXPECTED_THEOREM_IDS = ["YM-A", "YM-B", "YM-C", "YM-D", "YM-E"]


def run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--repo-root", str(REPO_ROOT), *args],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )


def load_json() -> dict[str, Any]:
    result = run_script()
    assert result.returncode == 0, result.stdout + result.stderr
    return json.loads(result.stdout)


def test_json_shape_and_exact_theorem_ids() -> None:
    payload = load_json()

    assert payload["agenda"] == "ym_missing_math_theorem_agenda"
    assert payload["ok"] is True
    assert payload["fail_closed"] is True
    assert payload["theorem_ids"] == EXPECTED_THEOREM_IDS
    assert [row["theorem_id"] for row in payload["theorems"]] == EXPECTED_THEOREM_IDS

    for row in payload["theorems"]:
        assert isinstance(row["statement"], str) and row["statement"]
        assert isinstance(row["symbolic_conclusion"], str) and row["symbolic_conclusion"]
        assert isinstance(row["required_inputs"], list) and row["required_inputs"]
        assert "missing_estimates" in row
        assert "authority_inputs" in row
        assert isinstance(row["downstream_unlocks"], list) and row["downstream_unlocks"]
        assert isinstance(row["status"], str) and row["status"]
        assert row["evidence_ok"] is True
        assert row["evidence"]


def test_all_promotion_flags_are_false() -> None:
    payload = load_json()

    assert payload["promotion_allowed"] is False
    assert payload["clay_promotion"] is False
    for row in payload["theorems"]:
        assert row["promotion_allowed"] is False
        assert row["clay_promotion"] is False


def test_ym_b_preserves_authority_and_repo_native_distinction() -> None:
    payload = load_json()
    ym_b = next(row for row in payload["theorems"] if row["theorem_id"] == "YM-B")

    option_paths = ym_b["option_paths"]
    by_option = {option["option"]: option for option in option_paths}
    assert by_option["A"]["kind"] == "authority-backed"
    assert by_option["A"]["status"] == "authority-intake"
    assert by_option["B"]["kind"] == "repo-native-open"
    assert by_option["B"]["status"] == "diagnostic-not-theorem"

    evidence_text = json.dumps(ym_b, sort_keys=True)
    assert "Balaban Option A theorem-intake boundary" in evidence_text
    assert "Option B B4 trace-norm consequence boundary" in evidence_text
    assert "B4TraceNormConvergenceFromSummability" in evidence_text


def test_markdown_includes_all_theorem_ids() -> None:
    result = run_script("--format", "md")
    assert result.returncode == 0, result.stdout + result.stderr

    for theorem_id in EXPECTED_THEOREM_IDS:
        assert theorem_id in result.stdout
    assert "HamiltonianDominatesDefectPlusHolonomy" in result.stdout
    assert "H3aTraceNormTransfer" in result.stdout
    assert "RP/OS/Wightman reconstruction compatibility" in result.stdout
