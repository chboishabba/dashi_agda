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
    / "Interop"
    / "FiniteSelectionMiningTermination.agda"
)
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def run_agda(path: Path) -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "-i", ".", str(path.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), "missing finite selection mining termination receipt"
    return RECEIPT.read_text(encoding="utf-8")


def test_finite_selection_mining_termination_typechecks(receipt_text: str) -> None:
    assert receipt_text
    run_agda(RECEIPT)


def test_finite_selection_mining_termination_core_surface(
    receipt_text: str,
) -> None:
    required_terms = (
        "data Artifact",
        "rawArtifact",
        "selectedArtifact",
        "minedFixedArtifact",
        "generatorCandidates",
        "bestCandidate",
        "canonicalSelectedResult",
        "canonicalSelectedResultIsMined",
        "canonicalTransition",
        "L-nonincrease",
        "twoStepCanonicalMiningReachesFixed",
        "CanonicalFiniteFixedPoint",
        "finiteSelectionMiningTerminationReceipt",
    )
    for term in required_terms:
        assert term in receipt_text, term


def test_finite_selection_mining_governance_flags(receipt_text: str) -> None:
    true_flags = (
        "finiteSelectionTerminates",
        "jmdCrankMiningVocabularyImported",
    )
    for name in true_flags:
        assert agda_bool_assignment(receipt_text, name, True), name

    false_flags = (
        "crankMiningPromotedAsDASHIClaim",
        "clayPromotion",
    )
    for name in false_flags:
        assert agda_bool_assignment(receipt_text, name, False), name
        assert not agda_bool_assignment(receipt_text, name, True), name


def test_crank_mining_is_bridge_vocabulary_not_dashi_promotion(
    receipt_text: str,
) -> None:
    required_boundaries = (
        "JMD bridge vocabulary",
        "imported vocabulary only",
        "not DASHI theorem promotion",
        "ImportedBridgeVocabulary",
        "jmdCrankMiningVocabulary",
    )
    for boundary in required_boundaries:
        assert boundary in receipt_text, boundary

    assert agda_bool_assignment(receipt_text, "crankMiningPromotedAsDASHIClaim", False)
    assert agda_bool_assignment(receipt_text, "clayPromotion", False)


def test_receipt_is_integrated_through_everything_without_promotion(
    receipt_text: str,
) -> None:
    assert receipt_text
    text = EVERYTHING.read_text(encoding="utf-8")
    assert "import DASHI.Interop.FiniteSelectionMiningTermination" in text
    assert agda_bool_assignment(receipt_text, "crankMiningPromotedAsDASHIClaim", False)
    assert agda_bool_assignment(receipt_text, "clayPromotion", False)
