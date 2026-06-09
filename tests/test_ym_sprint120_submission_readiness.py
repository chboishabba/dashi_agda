from __future__ import annotations

import json
import subprocess
from collections import Counter
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint120_submission_readiness_plan.py"
SUMMARY_NAME = "ym_sprint120_submission_readiness_summary.json"
PLAN_NAME = "ym_sprint120_submission_readiness_plan.md"


def run_script(tmp_path: Path) -> dict:
    out_dir = tmp_path / "readiness"
    result = subprocess.run(
        [
            "python",
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=True,
        text=True,
        capture_output=True,
    )
    assert "wrote" in result.stdout
    summary_path = out_dir / SUMMARY_NAME
    assert summary_path.exists()
    return json.loads(summary_path.read_text())


def test_submission_readiness_has_all_leaves_and_dispatch_rounds(tmp_path: Path) -> None:
    summary = run_script(tmp_path)

    obligations = {row["obligation_id"] for row in summary["obligations"]}
    expected = {
        "CC1", "CC2", "CC3", "CC4", "WC1", "WC2", "WC3p", "MC1", "MC2", "MC3", "MC4",
        "SC1", "SC2", "SC3", "SY1", "GG1", "FIN", "OS1",
    }
    assert obligations == expected
    assert all(row["status"] == "blocked" for row in summary["obligations"])
    assert summary["route_decision"] == "fail-closed"

    category_counts = Counter(row["category"] for row in summary["obligations"])
    assert category_counts == {"hard": 5, "medium": 10, "easy": 3}

    dependency_graph = {
        row["obligation_id"]: row["depends_on"] for row in summary["obligations"]
    }
    roots = [obligation_id for obligation_id, deps in dependency_graph.items() if not deps]
    assert roots == ["CC1"], "CC1 is the unique dependency root"

    expected_rounds = [
        ["CC1"],
        ["WC1", "CC2", "CC3", "CC4"],
        ["MC1", "WC2", "WC3p", "MC3"],
        ["SC1", "MC2", "MC4"],
        ["SC3", "SC2"],
        ["OS1", "SY1", "GG1"],
        ["FIN"],
    ]
    actual_rounds = [round_row["lanes"] for round_row in summary["rounds_of_six"]]
    assert actual_rounds == expected_rounds
    assert all(len(lanes) <= 6 for lanes in actual_rounds)

    completed: set[str] = set()
    for lanes in actual_rounds:
        for obligation_id in lanes:
            assert set(dependency_graph[obligation_id]) <= completed
        completed.update(lanes)
    assert completed == obligations


def test_submission_readiness_generates_markdown(tmp_path: Path) -> None:
    out_dir = tmp_path
    result = subprocess.run(
        [
            "python",
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=True,
        text=True,
        capture_output=True,
    )
    assert (out_dir / PLAN_NAME).exists()
    report = (out_dir / PLAN_NAME).read_text()
    assert "Sprint 120 Submission Readiness Plan" in report
    assert "Dispatch plan" in report
    assert "CC1" in report
    assert "round" in result.stdout.lower()
