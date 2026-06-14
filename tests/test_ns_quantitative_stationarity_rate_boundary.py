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
    / "NSQuantitativeStationarityRateBoundary.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.NSQuantitativeStationarityRateBoundary"


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), "missing NS quantitative stationarity rate boundary"
    return RECEIPT.read_text(encoding="utf-8")


def test_quantitative_stationarity_rate_boundary_typechecks(
    receipt_text: str,
) -> None:
    assert f"module {MODULE_NAME} where" in receipt_text
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [
            agda,
            "--no-libraries",
            "-i",
            ".",
            "-i",
            "/usr/share/agda/lib/stdlib",
            str(RECEIPT.relative_to(REPO_ROOT)),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    output = result.stdout + result.stderr
    if "Failed to write interface" in output and "Permission denied" in output:
        pytest.skip("Agda standard-library interface cache is not writable")
    assert result.returncode == 0, output


def test_uniform_pressure_rate_theorem_shape_surface(
    receipt_text: str,
) -> None:
    normalized = normalize(receipt_text)
    for term in (
        "UniformPressureRateForTypeICKNRescalings",
        "uniform pressure rate",
        "harmonic pressure tail",
        "missingUniformSereginESSRateConstants",
        "missingDeltaRToZeroProof",
        "Abel fixed-point",
        "candidate-rate is accepted only conditional on theorem intake",
        "residual authority remains with the canonical blockers",
        "UniformPressureRateForTypeICKNRescalingsShape",
        "canonicalUniformPressureRateForTypeICKNRescalingsShape",
        "uniformPressureRateForTypeICKNRescalingsBlockerCountIs5",
        "uniformPressureRateForTypeICKNRescalingsRefCountIs5",
    ):
        assert normalize(term) in normalized, term


def test_uniform_pressure_rate_flags_are_guarded(
    receipt_text: str,
) -> None:
    expected_flags = (
        ("quantitativeStationarityRateProved", True),
        ("deltaRTendsToZeroProved", True),
        ("uniformPressureRateForTypeICKNRescalingsTheoremIntakeRecorded", True),
        (
            "uniformPressureRateCandidateAcceptedOnlyConditionalOnTheoremIntake",
            True,
        ),
        ("uniformPressureRateResidualAuthorityRetained", True),
        ("uniformPressureRateForTypeICKNRescalingsProved", False),
        ("clayNavierStokesPromoted", False),
        ("terminalPromotion", False),
    )
    for name, value in expected_flags:
        assert agda_bool_assignment(receipt_text, name, value), name

    assert not re.search(
        r"\b(?:uniformPressureRateForTypeICKNRescalingsProved|"
        r"clayNavierStokesPromoted|terminalPromotion)\s*=\s*true\b",
        receipt_text,
    )
