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
    / "YMALocalArithmeticIntegrationBoundary.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.YMALocalArithmeticIntegrationBoundary"

CHILD_MODULES = (
    "DASHI.Physics.Closure.YMAKillingBoundaryLocalArithmetic",
    "DASHI.Physics.Closure.YMAHolonomyWilsonLocalArithmetic",
    "DASHI.Physics.Closure.YMAKingBochnerAuthorityBoundary",
    "DASHI.Physics.Closure.YMAFiniteDominationArithmeticComposite",
    "DASHI.Physics.Closure.ClaySubmissionCandidateMathBoundary",
)


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


def test_integration_boundary_imports_expected_child_modules() -> None:
    text = read_boundary()
    assert text.splitlines()[0] == f"module {MODULE_NAME} where"

    for child_module in CHILD_MODULES:
        assert f"import {child_module}" in text


def test_integration_boundary_records_aggregate_flags_fail_closed() -> None:
    text = read_boundary()

    assert has_bool_evidence(text, ("all", "local", "arithmetic", "inputs", "recorded"), True)
    assert has_bool_evidence(text, ("arithmetic", "promotes", "clay"), False)
    assert has_bool_evidence(text, ("integration", "boundary", "recorded"), True)

    for terms in (
        ("killing", "promotes", "clay"),
        ("holonomy", "wilson", "promotes", "clay"),
        ("king", "bochner", "promotes", "clay"),
        ("finite", "domination", "promotes", "clay"),
        ("clay", "submission", "candidate", "promotes", "clay"),
    ):
        assert has_bool_evidence(text, terms, False), terms

    forbidden_true_flags = [
        name
        for name, assigned in bool_assignments(text)
        if assigned == "true" and "promotes_clay" in normalize(name)
    ]
    assert forbidden_true_flags == []


def test_integration_boundary_records_required_receipt_terms() -> None:
    text = read_boundary()
    normalized = normalize(text)

    for term in (
        "KillingBoundaryLocalArithmetic",
        "HolonomyWilsonLocalArithmetic",
        "KingBochnerAuthorityBoundary",
        "FiniteDominationArithmeticComposite",
        "ClaySubmissionCandidateMath",
        "allLocalArithmeticInputsRecordedIsTrue",
        "arithmeticPromotesClayIsFalse",
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


def test_integration_boundary_typechecks_with_child_modules() -> None:
    run_agda_no_libraries()
