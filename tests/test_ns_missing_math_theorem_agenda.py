from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_missing_math_theorem_agenda.py"
EXPECTED_THEOREM_IDS = ["NS-A", "NS-B", "NS-C", "NS-D", "NS-E"]
EXPECTED_NAMES = {
    "NS-A": "AbelTriadicDefectMeasureConstruction",
    "NS-B": "LeiRenTianOutputSupportTransferToAbelMeasure",
    "NS-C": "NSTypeIBlowupKappaBiasBound",
    "NS-D": "PointwiseToAbelStretchingTransfer",
    "NS-E": "ClosureChainA5A9",
}


def walk(value: Any):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--repo-root", str(REPO_ROOT), *args],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )


def bool_values(payload: Any, key: str) -> list[bool]:
    return [
        item[key]
        for item in walk(payload)
        if isinstance(item, dict) and isinstance(item.get(key), bool)
    ]


def test_ns_missing_math_theorem_agenda_json_shape_and_fail_closed_flags() -> None:
    result = run_script()
    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads(result.stdout)

    assert payload["ok"] is True
    assert payload["fail_closed"] is True
    assert payload["theorem_ids"] == EXPECTED_THEOREM_IDS
    assert payload["promotion_allowed"] is False
    assert payload["clay_promotion"] is False
    assert payload["summary"]["proof_claimed"] is False
    assert payload["summary"]["target_count"] == 5

    targets = payload["targets"]
    assert [target["theorem_id"] for target in targets] == EXPECTED_THEOREM_IDS
    assert {target["theorem_id"]: target["theorem_name"] for target in targets} == EXPECTED_NAMES

    for target in targets:
        assert target["promotion_allowed"] is False
        assert target["clay_promotion"] is False
        assert target["evidence_ok"] is True
        assert target["status"] == "fail_closed_marker_validated_not_proved"
        assert target["theorem_statement"]
        assert target["symbolic_conclusion"]
        assert target["required_inputs"]
        assert target["missing_estimates"]
        assert target["downstream_unlocks"]
        assert target["evidence"]
        assert all(evidence["present"] is True for evidence in target["evidence"])

    assert all(value is False for value in bool_values(payload, "promotion_allowed"))
    assert all(value is False for value in bool_values(payload, "clay_promotion"))


def test_ns_missing_math_theorem_agenda_markdown_includes_exact_theorem_ids() -> None:
    result = run_script("--format", "md")
    assert result.returncode == 0, result.stdout + result.stderr
    text = result.stdout

    assert "fail_closed: `true`" in text
    assert "proof_claimed: `false`" in text
    for theorem_id in EXPECTED_THEOREM_IDS:
        assert f"## {theorem_id} " in text
    for theorem_name in EXPECTED_NAMES.values():
        assert theorem_name in text
