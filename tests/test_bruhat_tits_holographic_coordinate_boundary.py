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
    / "BruhatTitsHolographicCoordinateBoundary.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.BruhatTitsHolographicCoordinateBoundary"
FORBIDDEN_PATHS = (
    "DASHI/Everything.agda",
    "README.md",
    "TODO.md",
    "status.md",
)


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


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


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def bool_assignments(text: str) -> list[tuple[str, str]]:
    return re.findall(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b",
        text,
    )


def has_evidence(
    text: str,
    *,
    name_terms: tuple[str, ...],
    value: bool,
) -> bool:
    expected = "true" if value else "false"
    assignment = re.compile(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*=\s*"
        rf"{expected}\b"
    )
    for match in assignment.finditer(text):
        if all(normalize(term) in normalize(match.group(1)) for term in name_terms):
            return True

    proof_decl = re.compile(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*"
        r"([A-Za-z][A-Za-z0-9_']*)\s*≡\s*"
        rf"{expected}\b"
    )
    for match in proof_decl.finditer(text):
        normalized = normalize(" ".join(match.groups()))
        if all(normalize(term) in normalized for term in name_terms):
            return True
    return False


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), f"missing {RECEIPT.relative_to(REPO_ROOT)}"
    return RECEIPT.read_text(encoding="utf-8")


def test_bruhat_tits_holographic_coordinate_boundary_typechecks(
    receipt_text: str,
) -> None:
    assert MODULE_NAME in receipt_text
    run_agda(RECEIPT)


def test_records_finite_coordinate_boundary_not_ontology(receipt_text: str) -> None:
    for term in (
        "data Depth",
        "record BulkCell",
        "data BoundaryPoint",
        "toyBoundaryProjection",
        "canonicalBruhatTitsHolographicCoordinateBoundary",
        "CoordinateBoundaryRole",
        "finiteCutoffCoordinate",
        "regularizationBoundary",
        "toyProjectionBoundary",
    ):
        assert term in receipt_text

    assert has_evidence(
        receipt_text,
        name_terms=("locality", "toy"),
        value=True,
    )
    assert has_evidence(
        receipt_text,
        name_terms=("tree", "coordinate", "boundary"),
        value=True,
    )
    assert has_evidence(
        receipt_text,
        name_terms=("tree", "physical", "ontology"),
        value=False,
    )


def test_source_context_rows_are_context_only(receipt_text: str) -> None:
    for term in (
        "SourceContextRow",
        "qftSubspaceSourceRow",
        "pAdicAdSCFTSourceRow",
        "holographicDictionarySourceRow",
        "Effective field theories on subspaces of the Bruhat-Tits tree",
        "p-adic AdS/CFT",
        "JHEP06(2024)175 / arXiv",
        "JHEP05(2019)118 / arXiv",
        "arXiv:2402.03730",
        "arXiv:1605.01061",
        "arXiv:1812.06059",
    ):
        assert term in receipt_text

    assert receipt_text.count("contextOnly") >= 4
    assert receipt_text.count("importsPhysicalOntologyIsFalse") >= 1
    assert receipt_text.count("promotesHolographicQFTBridgeIsFalse") >= 1
    assert has_evidence(
        receipt_text,
        name_terms=("source", "context", "row", "count"),
        value=True,
    ) or "recordedSourceContextRowCountIsThree" in receipt_text


def test_promotion_and_clay_flags_stay_false(receipt_text: str) -> None:
    for name in (
        "holographicQFTBridgePromoted",
        "physicalOntologyClaim",
        "clayPromotion",
    ):
        assert agda_bool_assignment(receipt_text, name, False), name

    for terms in (
        ("holographic", "qft", "bridge", "promoted"),
        ("physical", "ontology", "claim"),
        ("clay", "promotion"),
    ):
        assert has_evidence(receipt_text, name_terms=terms, value=False)

    forbidden_true = [
        name
        for name, assigned in bool_assignments(receipt_text)
        if assigned == "true"
        and (
            "clay" in normalize(name)
            or "ontology" in normalize(name)
            or "promoted" in normalize(name)
        )
    ]
    assert forbidden_true == []


def test_control_card_and_edit_scope(receipt_text: str) -> None:
    normalized = normalize(receipt_text)
    for key in ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:"):
        assert normalize(key) in normalized

    status = subprocess.run(
        ["git", "status", "--short"],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert status.returncode == 0, status.stdout + status.stderr
    changed = {
        line[3:].strip()
        for line in status.stdout.splitlines()
        if line[:2].strip()
    }
    assert str(RECEIPT.relative_to(REPO_ROOT)) in changed
    assert "tests/test_bruhat_tits_holographic_coordinate_boundary.py" in changed
    for forbidden in FORBIDDEN_PATHS:
        # Other workers may have touched these files; this test documents that
        # this receipt is not integrated through those surfaces.
        assert forbidden not in receipt_text
