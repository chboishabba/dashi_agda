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
    / "ABIVerticalLiftBoundary.agda"
)


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
    assert RECEIPT.is_file(), "missing ABI vertical lift boundary receipt"
    return RECEIPT.read_text(encoding="utf-8")


def test_abi_vertical_lift_boundary_typechecks(receipt_text: str) -> None:
    assert receipt_text
    run_agda(RECEIPT)


def test_abi_vertical_lift_boundary_records_bridge_examples(
    receipt_text: str,
) -> None:
    required_terms = (
        "ABITransformKind",
        "elfToCar",
        "dagCborToIpld",
        "machineCodeToFractran",
        "agdaToLean",
        "ELF executable or object file",
        "CAR archive row",
        "DAG-CBOR block",
        "IPLD typed node",
        "FRACTRAN trace receipt",
        "Lean declaration row",
    )
    for term in required_terms:
        assert term in receipt_text, term


def test_abi_vertical_lift_boundary_keeps_sources_context_only(
    receipt_text: str,
) -> None:
    required_terms = (
        "Kolmogorov invariance theorem",
        "Wu 2026 semantic AIT",
        "context-only",
        "canonicalABIContextRows",
    )
    for term in required_terms:
        assert term in receipt_text, term

    assert agda_bool_assignment(receipt_text, "contextOnly", True)
    assert agda_bool_assignment(receipt_text, "externalAuthorityAccepted", False)


def test_abi_vertical_lift_boundary_flags_are_fail_closed(
    receipt_text: str,
) -> None:
    true_flags = (
        "verticalPreservesSemantics",
        "boundedOverheadRecorded",
    )
    for name in true_flags:
        assert agda_bool_assignment(receipt_text, name, True), name

    false_flags = (
        "exactKolmogorovSemanticTheorem",
        "semanticAITExternalAuthorityAccepted",
        "physicalPromotion",
        "exactEquivalencePromoted",
    )
    for name in false_flags:
        assert agda_bool_assignment(receipt_text, name, False), name

    assert not re.search(
        r"\b(?:exactKolmogorovSemanticTheorem|"
        r"semanticAITExternalAuthorityAccepted|"
        r"physicalPromotion|exactEquivalencePromoted)"
        r"\s*=\s*true\b",
        receipt_text,
    )
