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
    / "UCTPromotionEvidenceResidualBoundary.agda"
)


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def bool_assignments(text: str) -> dict[str, str]:
    return dict(
        re.findall(
            r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b",
            text,
        )
    )


def run_agda(path: Path) -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "--no-libraries", str(path.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    output = result.stdout + result.stderr
    assert result.returncode == 0, output


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), "missing UCT promotion-evidence residual boundary"
    return RECEIPT.read_text(encoding="utf-8")


def test_uct_promotion_evidence_residual_boundary_typechecks(
    receipt_text: str,
) -> None:
    assert "UCTPromotionEvidenceResidualBoundary" in receipt_text
    run_agda(RECEIPT)


def test_uct_dependency_chain_records_live_wall_and_consumers(
    receipt_text: str,
) -> None:
    expected_order = [
        "uct1OverlapResidualPDE",
        "uct2EllipticityParabolicityWitness",
        "uct3CarlemanUniqueContinuationIntake",
        "uct4CrossTermNullity",
        "uct5ModuloNullLinearity",
        "uct6FourPointCancellation",
        "uct7Parallelogram",
        "uct8JordanVonNeumann",
    ]
    row_block = receipt_text.split("canonicalUCTPromotionEvidenceRows =", 1)[1]
    row_block = row_block.split("uctPromotionEvidenceRowCount", 1)[0]
    positions = [row_block.index(name) for name in expected_order]
    assert positions == sorted(positions)

    for marker in (
        "uct1ResidualPDESpecificationRecorded",
        "uct2EllipticityOrParabolicityClassRecorded",
        "uct3CarlemanUniqueContinuationRecorded",
        "uct4CrossTermNullityLivePromotionEvidenceWall",
        "moduloNullLinearityConsumer",
        "fourPointCancellationConsumer",
        "parallelogramConsumer",
        "jordanVonNeumannAdapterConsumer",
    ):
        assert marker in receipt_text

    assert "uctPromotionEvidenceRowCountIs8" in receipt_text
    assert "canonicalUCTPromotionEvidenceRows" in receipt_text
    assert "livePromotionEvidenceWall" in receipt_text
    assert "downstreamConsumerLocked" in receipt_text


def test_uct_promotion_flags_and_core_theorems_stay_false(
    receipt_text: str,
) -> None:
    assignments = bool_assignments(receipt_text)

    for name in (
        "uct1OverlapResidualPDETheoremProved",
        "uct2EllipticityParabolicityTheoremProved",
        "uct3CarlemanUniqueContinuationTheoremProved",
        "uct4CrossTermNullityTheoremProved",
        "uctPromoted",
        "terminalPromoted",
        "clayEligible",
    ):
        assert assignments[name] == "false", name

    for name in (
        "uct1ResidualPDESpecificationRecorded",
        "uct2EllipticityOrParabolicityClassRecorded",
        "uct3CarlemanUniqueContinuationRecorded",
        "uct4CrossTermNullityLivePromotionEvidenceWall",
    ):
        assert assignments[name] == "true", name

    forbidden_true_flags = [
        name
        for name, value in assignments.items()
        if value == "true"
        and (
            "promoted" in normalize(name)
            or "eligible" in normalize(name)
            or (
                "theorem" in normalize(name)
                and "recorded" not in normalize(name)
            )
        )
    ]
    assert forbidden_true_flags == []


def test_uct_receipt_imports_downstream_consumer_chain(receipt_text: str) -> None:
    for imported in (
        "UnificationGluingModuloNullLinearityCompositeBoundary",
        "UnificationFourPointCancellationFromCrossTermNullityBoundary",
        "UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary",
    ):
        assert imported in receipt_text

    for proof in (
        "canonicalModuloNullTerminalPromotionFalse",
        "canonicalModuloNullClayPromotionFalse",
        "canonicalRouteFourPointCancellationStillOpen",
        "canonicalRouteParallelogramStillOpen",
        "canonicalRouteTerminalPromotionFalse",
        "provedStillFalse",
    ):
        assert proof in receipt_text
