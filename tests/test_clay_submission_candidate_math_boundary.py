from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_PATH = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "ClaySubmissionCandidateMathBoundary.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.ClaySubmissionCandidateMathBoundary"


def read_boundary() -> str:
    assert AGDA_PATH.is_file(), AGDA_PATH.relative_to(REPO_ROOT).as_posix()
    return AGDA_PATH.read_text(encoding="utf-8")


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def bool_assignments(text: str) -> list[tuple[str, str]]:
    typed = re.findall(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b",
        text,
    )
    fields = re.findall(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*"
        r"(?:[A-Za-z][A-Za-z0-9_']*\s+)?"
        r"([A-Za-z][A-Za-z0-9_']*)\s*≡\s*(true|false)\b",
        text,
    )
    return typed + [(left + "_" + right, value) for left, right, value in fields]


def has_bool_evidence(text: str, terms: tuple[str, ...], value: bool) -> bool:
    expected = "true" if value else "false"
    normalized_terms = [normalize(term) for term in terms]
    for name, assigned in bool_assignments(text):
        normalized_name = normalize(name)
        if assigned == expected and all(term in normalized_name for term in normalized_terms):
            return True
    return False


def run_agda_no_libraries() -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "--no-libraries", str(AGDA_PATH.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_boundary_module_typechecks_with_builtin_only_agda() -> None:
    text = read_boundary()
    assert text.splitlines()[0] == f"module {MODULE_NAME} where"
    assert "import DASHI." not in text
    run_agda_no_libraries()


def test_boundary_records_latest_candidate_surfaces_and_anchors() -> None:
    text = read_boundary()
    normalized = normalize(text)

    for term in (
        "NSAStationarityCandidate",
        "NSCKappaBiasCandidate",
        "YMAFiniteDominationCandidate",
        "W_r energy ODE",
        "OU bias balance",
        "Bochner-Weitzenbock domination",
        "YM-A local calculation",
        "ymAConstantsLocallyComputable=true",
        "ymAArithmeticObstructionAbsent=true",
        "ymAOperatorTheoremStillMissing=true",
        "ymAH3aStillMissing=true",
    ):
        assert normalize(term) in normalized, term


def test_boundary_keeps_candidates_recorded_but_not_promoted_or_eligible() -> None:
    text = read_boundary()

    for terms in (
        ("nsa", "candidate", "recorded"),
        ("nsc", "candidate", "recorded"),
        ("yma", "candidate", "recorded"),
        ("ym", "a", "constants", "locally", "computable"),
        ("ym", "a", "arithmetic", "obstruction", "absent"),
        ("ym", "a", "operator", "theorem", "still", "missing"),
        ("ym", "a", "h3a", "still", "missing"),
        ("boundary", "recorded"),
    ):
        assert has_bool_evidence(text, terms, True), terms

    for terms in (
        ("nsa", "proof", "promoted"),
        ("nsc", "proof", "promoted"),
        ("yma", "proof", "promoted"),
        ("yma", "arithmetic", "proof", "promoted"),
        ("boundary", "proof", "promoted"),
        ("nsa", "clay", "eligible"),
        ("nsc", "clay", "eligible"),
        ("yma", "clay", "eligible"),
        ("yma", "arithmetic", "clay", "eligible"),
        ("boundary", "clay", "eligible"),
    ):
        assert has_bool_evidence(text, terms, False), terms

    forbidden_true_flags = [
        name
        for name, assigned in bool_assignments(text)
        if assigned == "true"
        and any(token in normalize(name) for token in ("promoted", "eligible"))
    ]
    assert forbidden_true_flags == []


def test_boundary_records_required_dependency_edges_and_control_card() -> None:
    text = read_boundary()
    normalized = normalize(text)

    for term in (
        "NS-C dependsOn NS-A",
        "YM Clay dependsOn H3a",
        "nscDependsOnNSARecordedIsTrue",
        "ymClayDependsOnH3aRecordedIsTrue",
        "ymAConstantsLocallyComputableRecordedIsTrue",
        "ymAArithmeticObstructionAbsentRecordedIsTrue",
        "ymAOperatorTheoremStillMissingRecordedIsTrue",
        "ymAH3aStillMissingRecordedIsTrue",
        "ymAArithmeticProofPromotedIsFalse",
        "ymAArithmeticClayEligibleIsFalse",
        "O:",
        "R:",
        "C:",
        "S:",
        "L:",
        "P:",
        "G:",
        "F:",
    ):
        assert normalize(term) in normalized, term
