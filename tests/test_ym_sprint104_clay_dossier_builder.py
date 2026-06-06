from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint104_clay_dossier_builder.py"
MODULE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "YMSprint104ClayCandidateDossierBuilder.agda"
)
SUMMARY_NAME = "ym_sprint104_clay_dossier_builder_summary.json"
FORBIDDEN = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
)


def run_script(repo_root: Path, out_dir: Path) -> dict:
    subprocess.run(
        [
            "python",
            str(SCRIPT),
            "--repo-root",
            str(repo_root),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=True,
    )
    return json.loads((out_dir / SUMMARY_NAME).read_text())


def write_sprint_module(repo_root: Path, sprint: int, name: str, text: str) -> None:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    (module_dir / f"YMSprint{sprint}{name}.agda").write_text(text)


def write_summary(repo_root: Path, sprint: int, data: dict) -> None:
    out_dir = repo_root / "outputs" / f"ym_sprint{sprint}_fixture"
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / f"ym_sprint{sprint}_fixture_summary.json").write_text(
        json.dumps(data) + "\n"
    )


def populate_fixture_repo(repo_root: Path, *, promote: bool = False) -> None:
    for sprint in range(91, 104):
        write_sprint_module(
            repo_root,
            sprint,
            "Fixture",
            f"""\
module DASHI.Physics.Closure.YMSprint{sprint}Fixture where

open import Agda.Builtin.Bool using (Bool; false; true)

clayYangMillsPromoted : Bool
clayYangMillsPromoted = {"true" if promote and sprint == 103 else "false"}

fixtureEvidence : Agda.Builtin.Bool.Bool
fixtureEvidence = true

GaugeCovariantDobrushinComparison : Agda.Builtin.Bool.Bool
GaugeCovariantDobrushinComparison = true

WC3UniformClusterSummability : Agda.Builtin.Bool.Bool
WC3UniformClusterSummability = true

ContinuumLimitMassGap : Agda.Builtin.Bool.Bool
ContinuumLimitMassGap = true

RGInvariantPhysicalScale : Agda.Builtin.Bool.Bool
RGInvariantPhysicalScale = true

Nontrivial4DSU3YangMillsMeasure : Agda.Builtin.Bool.Bool
Nontrivial4DSU3YangMillsMeasure = true

SU3Evidence : Agda.Builtin.Bool.Bool
SU3Evidence = true

externalAcceptanceTokenAvailable : Agda.Builtin.Bool.Bool
externalAcceptanceTokenAvailable = false
""",
        )
        write_summary(
            repo_root,
            sprint,
            {
                "sprint": sprint,
                "route_decision": "fixture",
                "clayYangMillsPromoted": False,
            },
        )
    subprocess.run(
        ["git", "init"],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    (repo_root / "README.md").write_text("fixture\n")
    subprocess.run(
        ["git", "add", "README.md"],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Sprint Fixture",
            "-c",
            "user.email=sprint-fixture@example.invalid",
            "commit",
            "-m",
            "fixture",
        ],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    subprocess.run(
        ["git", "tag", "sprint-103-receipt-freeze"],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def test_sprint104_builder_accepts_evidence_backed_fixture(tmp_path: Path) -> None:
    populate_fixture_repo(tmp_path)
    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == (
        "SPRINT104_COMPLETE_DOSSIER_BUILDER_WITH_BLOCKED_CLAY_GAPS"
    )
    assert summary["freeze"]["present"] is True
    assert summary["module_count"] == 13
    assert summary["summary_count"] == 13
    assert len(summary["dependency_graph"]["nodes"]) == 26
    assert all(section["evidence"] for section in summary["dossier_sections"])
    assert {
        gap["gap_id"] for gap in summary["blocked_clay_requirements"]
    } == {
        "blockedWightmanDistributions",
        "blockedPoincareCovariance",
        "blockedSpectrumCondition",
        "blockedAllCompactSimpleG",
        "blockedNonCircularMassGapProof",
    }
    assert summary["clay_promotion"]["no_clay_promotion"] is True


def test_sprint104_builder_fails_closed_for_promotion(tmp_path: Path) -> None:
    populate_fixture_repo(tmp_path, promote=True)
    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "SPRINT104_FAIL_CLOSED"
    assert summary["clay_promotion"]["clayYangMillsPromoted"] is True
    assert summary["clay_promotion"]["no_clay_promotion"] is False


def test_sprint104_formal_surface_has_no_placeholder_tokens() -> None:
    text = MODULE.read_text()

    for token in FORBIDDEN:
        assert token not in text
    assert "clayYangMillsPromoted = true" not in text
    assert "clayYangMillsPromoted = false" in text
    assert "blockedWightmanDistributions" in text
    assert "blockedAllCompactSimpleG" in text
    assert "blockedNonCircularMassGapProof" in text
    assert "data " not in text


def test_sprint104_real_repo_outputs_have_evidence_and_blockers(tmp_path: Path) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert summary["route_decision"] == (
        "SPRINT104_COMPLETE_DOSSIER_BUILDER_WITH_BLOCKED_CLAY_GAPS"
    )
    assert all(section["evidence"] for section in summary["dossier_sections"])
    assert len(summary["blocked_clay_requirements"]) == 5
    assert len(summary["red_team_checklist"]) >= 4
    assert summary["clay_promotion"]["no_clay_promotion"] is True
