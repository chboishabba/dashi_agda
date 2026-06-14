from __future__ import annotations

import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_CANDIDATES = (
    REPO_ROOT / "scripts" / "ns_abel_defect_measure_agenda.py",
    REPO_ROOT / "scripts" / "ns_abel_triadic_defect_measure_agenda.py",
)
EXPECTED_GATES = {"A1.1", "A1.2", "A1.3", "A3.1", "A3.2", "A3.3", "A3.4"}


def agenda_script() -> Path:
    for path in SCRIPT_CANDIDATES:
        if path.exists():
            return path
    candidates = ", ".join(str(path.relative_to(REPO_ROOT)) for path in SCRIPT_CANDIDATES)
    raise AssertionError(f"missing NS Abel agenda script; expected one of: {candidates}")


def first_json(text: str) -> Any:
    decoder = json.JSONDecoder()
    for index, char in enumerate(text):
        if char not in "[{":
            continue
        try:
            value, _ = decoder.raw_decode(text[index:])
        except json.JSONDecodeError:
            continue
        return value
    raise AssertionError(f"no JSON object found in output:\n{text[-1000:]}")


def run_agenda() -> Any:
    result = subprocess.run(
        [
            sys.executable,
            str(agenda_script()),
            "--format",
            "json",
            "--max-evidence-files",
            "2",
        ],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr or result.stdout
    return first_json(result.stdout)


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for item in value.values():
            yield from walk(item)
    elif isinstance(value, list):
        for item in value:
            yield from walk(item)


def text_of(value: Any) -> str:
    if isinstance(value, dict):
        return " ".join(text_of(item) for item in value.values())
    if isinstance(value, list):
        return " ".join(text_of(item) for item in value)
    return str(value)


def normalized_key(key: str) -> str:
    return "".join(char if char.isalnum() else "_" for char in key.lower()).strip("_")


def assert_no_positive_promotion_flags(payload: Any) -> None:
    bad: list[tuple[str, Any]] = []
    for value in walk(payload):
        if not isinstance(value, dict):
            continue
        for key, item in value.items():
            key_lower = key.lower()
            if "promotion" not in key_lower and "promoted" not in key_lower:
                continue
            safe_true = any(
                marker in key_lower
                for marker in ("no_", "non_", "false", "blocked", "forbidden", "fail_closed")
            )
            if item is True and not safe_true:
                bad.append((key, item))
            if isinstance(item, str) and item.lower() in {"true", "promoted", "promotion"}:
                bad.append((key, item))
    assert bad == []


def assert_statuses_non_promoting(payload: Any) -> None:
    bad: list[str] = []
    for value in walk(payload):
        if not isinstance(value, dict):
            continue
        for key, item in value.items():
            if "status" not in key.lower() or not isinstance(item, str):
                continue
            status = item.lower()
            if any(word in status for word in ("promoted", "promotion", "proved")) and not any(
                marker in status for marker in ("non", "no_", "no-", "not", "false", "blocked", "guard", "boundary")
            ):
                bad.append(item)
    assert bad == []


def assert_task_counts_match_lists(payload: Any) -> None:
    assert isinstance(payload, dict)
    gate_rows = payload.get("gate_rows")
    assert isinstance(gate_rows, list)
    assert len(gate_rows) == 7
    assert all(row["marker_present"] is True for row in gate_rows)
    assert payload["checks"]["all_gate_markers_present"] is True


def assert_kappa_moment_diagnostics(payload: Any) -> None:
    assert isinstance(payload, dict)
    normal_form = payload.get("finite_normal_form")
    assert isinstance(normal_form, dict)
    assert normal_form["kappa_distribution"] == "arcsine"
    assert math.isclose(float(normal_form["E[kappa^2]"]), 0.5, rel_tol=0.0, abs_tol=1.0e-12)
    assert math.isclose(float(normal_form["E[kappa^4]"]), 0.375, rel_tol=0.0, abs_tol=1.0e-12)
    assert normal_form["lambda_squared_exact"] == "11/60"
    assert math.isclose(
        float(normal_form["kappa_bias_constant_sqrt_11_60"]),
        math.sqrt(11.0 / 60.0),
        rel_tol=0.0,
        abs_tol=1.0e-12,
    )


def test_ns_abel_agenda_contains_a1_a3_gates_and_counts() -> None:
    payload = run_agenda()
    text = text_of(payload)

    assert EXPECTED_GATES <= {gate for gate in EXPECTED_GATES if gate in text}
    assert_task_counts_match_lists(payload)


def test_ns_abel_agenda_keeps_kappa_and_statuses_non_promoting() -> None:
    payload = run_agenda()

    assert_kappa_moment_diagnostics(payload)
    assert_no_positive_promotion_flags(payload)
    assert_statuses_non_promoting(payload)
