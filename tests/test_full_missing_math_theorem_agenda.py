from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "full_missing_math_theorem_agenda.py"
DOMAIN_SCRIPTS = (
    REPO_ROOT / "scripts" / "ns_missing_math_theorem_agenda.py",
    REPO_ROOT / "scripts" / "ym_missing_math_theorem_agenda.py",
    REPO_ROOT / "scripts" / "uct_missing_math_theorem_agenda.py",
)
EXPECTED_COUNTS = {"NS": 5, "YM": 5, "UCT": 8}


def require_domain_surfaces() -> None:
    missing = [str(path.relative_to(REPO_ROOT)) for path in DOMAIN_SCRIPTS if not path.exists()]
    if missing:
        raise unittest.SkipTest("domain theorem agenda scripts not present yet: " + ", ".join(missing))


def run_agenda(*args: str) -> subprocess.CompletedProcess[str]:
    require_domain_surfaces()
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for item in value.values():
            yield from walk(item)
    elif isinstance(value, list):
        for item in value:
            yield from walk(item)


def payload() -> dict[str, Any]:
    result = run_agenda()
    assert result.returncode == 0, result.stderr or result.stdout
    data = json.loads(result.stdout)
    assert isinstance(data, dict)
    return data


def test_full_agenda_counts_and_theorem_ids_are_exact() -> None:
    data = payload()

    assert data["fail_closed"] is True
    assert data["counts_by_domain"] == EXPECTED_COUNTS
    assert data["expected_counts"] == EXPECTED_COUNTS
    assert data["total_theorems"] == sum(EXPECTED_COUNTS.values())

    domains = data["domains"]
    assert set(domains) == set(EXPECTED_COUNTS)
    all_ids: list[str] = []
    for domain, expected_count in EXPECTED_COUNTS.items():
        rows = domains[domain]["theorems"]
        ids = [row["theorem_id"] for row in rows]
        assert len(rows) == expected_count
        assert len(ids) == len(set(ids))
        assert all(row["domain"] == domain for row in rows)
        all_ids.extend(ids)

    assert len(all_ids) == len(set(all_ids))


def test_full_agenda_all_promotion_flags_are_false() -> None:
    for item in walk(payload()):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if "promotion" in key.lower() or "promoted" in key.lower():
                assert value is False


def test_full_agenda_markdown_output() -> None:
    result = run_agenda("--format", "md")
    assert result.returncode == 0, result.stderr or result.stdout
    text = result.stdout

    assert text.startswith("# Full Missing Math Theorem Agenda\n")
    assert "| Domain | Count | Expected |" in text
    for domain, expected in EXPECTED_COUNTS.items():
        assert f"| {domain} | {expected} | {expected} |" in text
        assert f"## {domain}" in text
    assert "promotion_allowed: false" in text
    assert "clay_promotion: false" in text
    assert "terminal_promotion: false" in text
