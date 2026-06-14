from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
MODULE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "YMAKillingBoundaryLocalArithmetic.agda"
)

REQUIRED_STRINGS = (
    "module DASHI.Physics.Closure.YMAKillingBoundaryLocalArithmetic where",
    "piSquaredApprox",
    "rat 98696 10000",
    "su2GammaLowerBound",
    "rat 49348 10000",
    "su3GammaLowerBound",
    "rat 74022 10000",
    "su2KingGammaLowerBoundCleared",
    "su3KingGammaLowerBoundCleared",
    "su2CasimirAdjointRecorded",
    "su3CasimirAdjointRecorded",
    "su2BochnerConstantRecorded",
    "su3BochnerConstantRecorded",
    "su2C1MarginNumeratorRecorded",
    "444132",
    "su3C1MarginNumeratorRecorded",
    "666198",
    "c1MarginPositive",
    "O:",
    "R:",
    "C:",
    "S:",
    "L:",
    "P:",
    "G:",
    "F:",
)

TRUE_FLAGS = (
    "arithmeticRecorded",
    "kingAuthorityAcceptedAsArithmeticInput",
)

FAIL_CLOSED_FLAGS = (
    "domainClosureProved",
    "boundaryFluxCancellationProved",
    "selfAdjointQuotientHamiltonianProved",
    "clayYangMillsPromoted",
)


def module_text() -> str:
    return MODULE.read_text(encoding="utf-8")


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def test_ym_a_killing_boundary_local_arithmetic_typechecks_no_libraries() -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [
            agda,
            "--no-libraries",
            str(MODULE.relative_to(REPO_ROOT)),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_ym_a_killing_boundary_records_requested_arithmetic_rows() -> None:
    text = module_text()

    for required in REQUIRED_STRINGS:
        assert required in text, required

    assert "KingGammaLowerBoundCleared" in text
    assert "su2GammaRowEquivalentToNpiSquaredOverFour" in text
    assert "su3GammaRowEquivalentToNpiSquaredOverFour" in text
    assert "su2C1MarginEqualsNineTwentiethsGamma" in text
    assert "su3C1MarginEqualsNineTwentiethsGamma" in text


def test_ym_a_killing_boundary_fail_closed_flags_are_explicit() -> None:
    text = module_text()

    for name in TRUE_FLAGS:
        assert agda_bool_assignment(text, name, True), name

    for name in FAIL_CLOSED_FLAGS:
        assert agda_bool_assignment(text, name, False), name
        assert not agda_bool_assignment(text, name, True), name


def test_ym_a_killing_boundary_has_no_positive_promotion_flag() -> None:
    text = module_text()

    positive_promotion = re.compile(
        r"\b[A-Za-z][A-Za-z0-9_']*(?:Promoted|Promotion|Solved|Proved)"
        r"[A-Za-z0-9_']*\s*=\s*true\b"
    )
    offenders = [
        match.group(0)
        for match in positive_promotion.finditer(text)
        if "arithmeticRecorded" not in match.group(0)
    ]
    assert offenders == []
