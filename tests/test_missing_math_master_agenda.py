from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_CANDIDATES = (
    REPO_ROOT / "scripts" / "missing_math_master_agenda.py",
    REPO_ROOT / "scripts" / "master_missing_math_agenda.py",
)
EXPECTED_LANES = {
    "ns": ("ns", "navier", "stokes"),
    "ym": ("ym", "yang", "mills"),
    "unification": ("unification",),
}


def agenda_script() -> Path:
    for path in SCRIPT_CANDIDATES:
        if path.exists():
            return path
    candidates = ", ".join(str(path.relative_to(REPO_ROOT)) for path in SCRIPT_CANDIDATES)
    raise AssertionError(f"missing master agenda script; expected one of: {candidates}")


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
        [sys.executable, str(agenda_script()), "--format", "json"],
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


def dict_text(value: dict[str, Any]) -> str:
    return " ".join(str(item).lower() for item in value.values())


def lane_rows(payload: Any) -> list[dict[str, Any]]:
    rows = [
        value
        for value in walk(payload)
        if isinstance(value, dict)
        and any(key in value for key in ("lane", "lane_id", "lane_name", "paper", "track"))
    ]
    assert rows, "agenda emitted no lane-addressed rows"
    return rows


def lane_bucket(row: dict[str, Any]) -> str | None:
    text = dict_text(row)
    for lane, tokens in EXPECTED_LANES.items():
        if all(token in text for token in tokens):
            return lane
    return None


def assert_no_positive_promotion_flags(payload: Any) -> None:
    allowed_true_markers = ("no_", "non_", "blocked", "forbidden", "false", "absent", "guard")
    bad: list[tuple[str, Any]] = []
    for value in walk(payload):
        if not isinstance(value, dict):
            continue
        for key, item in value.items():
            key_lower = key.lower()
            if "promotion" not in key_lower and "promoted" not in key_lower:
                continue
            if item is True and not any(marker in key_lower for marker in allowed_true_markers):
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


def assert_task_counts_are_complete(payload: Any) -> None:
    walls = payload.get("walls") if isinstance(payload, dict) else None
    assert isinstance(walls, dict)
    assert {str(key) for key in walls} == {"NS", "YM", "Unification"}
    assert {str(key): len(value) for key, value in walls.items()} == {
        "NS": 10,
        "YM": 10,
        "Unification": 10,
    }
    for lane, rows in walls.items():
        task_ids = [row["task_id"] for row in rows]
        assert len(task_ids) == len(set(task_ids)), lane


def test_master_missing_math_agenda_has_all_three_non_promoting_lanes() -> None:
    payload = run_agenda()
    observed = {lane for row in lane_rows(payload) if (lane := lane_bucket(row)) is not None}

    assert observed == set(EXPECTED_LANES)
    assert_no_positive_promotion_flags(payload)
    assert_statuses_non_promoting(payload)


def test_master_missing_math_agenda_task_counts_are_complete() -> None:
    assert_task_counts_are_complete(run_agenda())
