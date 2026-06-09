from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_FILE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSMonodromyIntegralBoundFinite.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.NSMonodromyIntegralBoundFinite"
CONTROL_CARD_KEYS = ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:")


@pytest.fixture(scope="module")
def agda_text() -> str:
    assert AGDA_FILE.is_file(), f"missing Agda file: {AGDA_FILE.relative_to(REPO_ROOT)}"
    return AGDA_FILE.read_text(encoding="utf-8")


def run_agda(path: Path) -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, str(path.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def nat_assignment(text: str, name: str, value: int) -> bool:
    return re.search(rf"\b{re.escape(name)}\s*=\s*{value}\b", text) is not None


def test_ns_monodromy_integral_bound_finite_typechecks(agda_text: str) -> None:
    assert MODULE_NAME in agda_text
    run_agda(AGDA_FILE)


def test_ns_monodromy_integral_bound_finite_has_no_postulates_or_holes(
    agda_text: str,
) -> None:
    forbidden = (
        "postulate",
        "{!!}",
        "Set ?",
        "= ?",
        "TODO",
        "admit",
        "{-# TERMINATING #-}",
        "{-# NON_TERMINATING #-}",
    )
    lowered = agda_text.lower()
    assert "stub" not in lowered
    for token in forbidden:
        assert token not in agda_text, token


def test_ns_monodromy_integral_bound_finite_records_samples_and_constants(
    agda_text: str,
) -> None:
    for name in (
        "QuarterTurnSample",
        "theta0",
        "thetaPiOver2",
        "thetaPi",
        "theta3PiOver2",
        "encodedSinSquaredDefectValues",
        "finiteSinSquaredDefectSum",
        "finiteAverageDenominator",
        "finiteAverageSinSquared",
        "explicitPositiveLowerBoundHalf",
        "finiteAverageEqualsExplicitHalf",
        "finiteAverageAtLeastExplicitHalf",
        "rationalCrossProductEquality",
        "rationalLowerBoundByCrossProduct",
    ):
        assert name in agda_text, name

    assert "0 ∷ 1 ∷ 0 ∷ 1 ∷ []" in agda_text
    assert nat_assignment(agda_text, "quarterTurnSampleCount", 4)
    assert nat_assignment(agda_text, "finiteAverageDenominator", 4)
    assert "finiteSinSquaredDefectSumIsTwo" in agda_text
    assert "finiteAverageSinSquaredIsTwoOverFour" in agda_text
    assert "explicitPositiveLowerBoundHalfIsOneOverTwo" in agda_text
    assert "encodedRational 2 4" in agda_text
    assert "encodedRational 1 2" in agda_text
    assert "s≤s (s≤s (s≤s (s≤s z≤n)))" in agda_text


def test_ns_monodromy_integral_bound_finite_fail_closed_flags(
    agda_text: str,
) -> None:
    assert bool_assignment(agda_text, "quarterTurnDefectVectorRecorded", True)
    assert bool_assignment(agda_text, "finiteAverageLowerBoundEqualsOneHalf", True)
    assert bool_assignment(agda_text, "piOver8StyleContinuumTargetOnly", True)
    assert bool_assignment(
        agda_text,
        "topologicalStretchingLeakageFiniteSupport",
        True,
    )
    assert bool_assignment(
        agda_text,
        "continuumTopologicalStretchingLeakageLemma",
        False,
    )
    assert bool_assignment(agda_text, "clayNavierStokesPromoted", False)
    assert not bool_assignment(
        agda_text,
        "continuumTopologicalStretchingLeakageLemma",
        True,
    )
    assert not bool_assignment(agda_text, "clayNavierStokesPromoted", True)


def test_ns_monodromy_integral_bound_finite_rows_receipt_and_control_card(
    agda_text: str,
) -> None:
    for name in (
        "NSMonodromyFiniteSampleRow",
        "NSMonodromyFiniteBoundRow",
        "NSMonodromyContinuumConnectionRow",
        "NSMonodromyFiniteORCSLPGF",
        "NSMonodromyIntegralBoundFiniteReceipt",
        "canonicalNSMonodromyIntegralBoundFiniteReceipt",
    ):
        assert name in agda_text, name

    assert nat_assignment(agda_text, "nsMonodromyFiniteSampleRowCount", 4)
    assert nat_assignment(agda_text, "nsMonodromyFiniteBoundRowCount", 6)
    assert nat_assignment(agda_text, "nsMonodromyContinuumConnectionRowCount", 4)

    for key in CONTROL_CARD_KEYS:
        assert key in agda_text, key
