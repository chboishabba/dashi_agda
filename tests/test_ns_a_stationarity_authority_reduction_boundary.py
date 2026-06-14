from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSAStationarityAuthorityReductionBoundary.agda"
)
MODULE_NAME = (
    "DASHI.Physics.Closure.NSAStationarityAuthorityReductionBoundary"
)


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), "missing NS-A stationarity authority receipt"
    return RECEIPT.read_text(encoding="utf-8")


def test_ns_a_stationarity_authority_receipt_typechecks(receipt_text: str) -> None:
    assert f"module {MODULE_NAME} where" in receipt_text
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "--no-libraries", str(RECEIPT.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_ns_a_stationarity_authority_records_positive_route_flags(
    receipt_text: str,
) -> None:
    for name in (
        "NSAStationarityAuthorityReductionBoundaryRecorded",
        "A1BoundedMassAlreadyShaped",
        "A3StationarityDependsOnUniformSereginESSRate",
        "A3StationarityDependsOnHarmonicPressureTailRate",
        "A3StationarityDependsOnDeltaRToZero",
        "A3StationarityDependsOnAbelSummationClosure",
        "AbelTriadicStationarityRouteRecorded",
        "A3AuthorityReductionRouteRecorded",
    ):
        assert agda_bool_assignment(receipt_text, name, True), name

    for term in (
        "A1 bounded mass shaped",
        "uniform Seregin/ESS rate",
        "harmonic pressure tail rate",
        "delta_r -> 0",
        "Abel summation closure",
        "canonicalNSAAuthorityRouteSteps",
        "canonicalA3StationarityDependencies",
        "canonicalAbelTriadicReductionClauses",
    ):
        assert term in receipt_text, term


def test_ns_a_stationarity_authority_keeps_promotion_flags_false(
    receipt_text: str,
) -> None:
    for name in (
        "uniformSereginESSRateProved",
        "harmonicPressureTailRateProved",
        "deltaRToZeroBridgeProved",
        "abelSummationClosureProved",
        "a3StationarityAuthorityReductionProved",
        "nsAStationarityPromoted",
        "nsClayPromoted",
        "terminalPromotion",
        "clayNavierStokesPromoted",
    ):
        assert agda_bool_assignment(receipt_text, name, False), name

    assert not re.search(
        r"\b(?:nsAStationarityPromoted|nsClayPromoted|"
        r"terminalPromotion|clayNavierStokesPromoted)\s*=\s*true\b",
        receipt_text,
    )
