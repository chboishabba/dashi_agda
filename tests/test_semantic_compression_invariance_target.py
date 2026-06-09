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
    / "SemanticCompressionInvarianceTarget.agda"
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
        [agda, str(path.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), "missing semantic compression target receipt"
    return RECEIPT.read_text(encoding="utf-8")


def test_semantic_compression_target_typechecks(receipt_text: str) -> None:
    assert receipt_text
    run_agda(RECEIPT)


def test_semantic_compression_target_names_the_pipeline(receipt_text: str) -> None:
    required_terms = (
        "Semantic Compression Invariance",
        "Artifact/CID",
        "FRACTRAN trace",
        "FactorVec prime-geometry address",
        "MDL/post-entropy",
        "Observable",
        "Prediction/comparison receipt",
        "Compression.canonicalCompressionAdmissibilityReceipt",
    )
    for term in required_terms:
        assert term in receipt_text


def test_semantic_compression_target_is_fail_closed(receipt_text: str) -> None:
    true_flags = (
        "squareTyped",
        "semanticEquivalenceTyped",
        "semanticConservationSquareTyped",
    )
    for name in true_flags:
        assert agda_bool_assignment(receipt_text, name, True), name

    false_flags = (
        "exactCommutativityProved",
        "semanticConservationTheoremProved",
        "exactPostEntropyInvarianceProved",
        "epsilonPostEntropyInvarianceProved",
        "physicalProjectionPromoted",
        "terminalUnificationPromoted",
    )
    for name in false_flags:
        assert agda_bool_assignment(receipt_text, name, False), name

    assert not re.search(
        r"\b(?:semanticConservationTheoremProved|"
        r"exactPostEntropyInvarianceProved|"
        r"epsilonPostEntropyInvarianceProved|"
        r"physicalProjectionPromoted|terminalUnificationPromoted)"
        r"\s*=\s*true\b",
        receipt_text,
    )


def test_semantic_compression_target_imported_by_everything(
    receipt_text: str,
) -> None:
    assert receipt_text
    text = EVERYTHING.read_text(encoding="utf-8")
    assert "import DASHI.Interop.SemanticCompressionInvarianceTarget" in text
