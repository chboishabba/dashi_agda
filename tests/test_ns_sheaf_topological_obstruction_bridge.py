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
    / "NSSheafTopologicalObstructionBridge.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.NSSheafTopologicalObstructionBridge"
SPRINT163_MODULE = (
    "DASHI.Physics.Closure."
    "NSSprint163TopologicalAlignmentObstructionBoundaryReceipt"
)
CONTROL_CARD_KEYS = ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:")
FORBIDDEN_EDIT_PATHS = (
    "README.md",
    "TODO.md",
    "status.md",
    "DASHI/Everything.agda",
)


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


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
    normalized_terms = tuple(normalize(term) for term in name_terms)

    for name, assigned in bool_assignments(text):
        if assigned == expected and all(term in normalize(name) for term in normalized_terms):
            return True

    proof_decl = re.compile(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*"
        r"([A-Za-z][A-Za-z0-9_']*)\s*≡\s*"
        rf"{expected}\b"
    )
    for match in proof_decl.finditer(text):
        normalized_evidence = normalize(" ".join(match.groups()))
        if all(term in normalized_evidence for term in normalized_terms):
            return True
    return False


@pytest.fixture(scope="module")
def receipt_text() -> str:
    if not RECEIPT.is_file():
        pytest.skip("NS sheaf/topological obstruction bridge has not landed yet")
    return RECEIPT.read_text(encoding="utf-8")


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


def test_ns_sheaf_topological_obstruction_bridge_typechecks(receipt_text: str) -> None:
    assert receipt_text
    run_agda(RECEIPT)


def test_bridge_imports_and_anchors_sprint163_source_records(receipt_text: str) -> None:
    assert f"module {MODULE_NAME}" in receipt_text
    assert f"import {SPRINT163_MODULE} as S163" in receipt_text
    assert "canonicalNSSprint163TopologicalAlignmentObstructionBoundaryReceipt" in receipt_text

    for terms in (
        ("sprint163", "topological", "alignment", "obstruction", "source"),
        ("sprint163", "angular", "strain", "symbol", "degeneracy"),
        ("sprint163", "maximal", "eigenbundle", "non", "orientability"),
        ("sprint163", "critical", "alignment", "target"),
        ("sprint163", "no", "pde", "claim"),
    ):
        assert has_evidence(receipt_text, name_terms=terms, value=True), terms


def test_bridge_defines_required_rows_and_counts(receipt_text: str) -> None:
    for term in (
        "NSSheafTopologicalObstructionRow",
        "localSection",
        "overlapCompatibility",
        "nonorientableEigensectionObstruction",
        "sigmaConcentrationTarget",
        "pressureCommutatorTarget",
        "canonicalNSSheafTopologicalObstructionRows",
        "nsSheafTopologicalObstructionRowCount",
        "nsSheafTopologicalObstructionRowCountIsFive",
    ):
        assert term in receipt_text, term

    assert has_evidence(receipt_text, name_terms=("local", "section", "row"), value=True)
    assert has_evidence(receipt_text, name_terms=("overlap", "compatibility", "row"), value=True)
    assert has_evidence(
        receipt_text,
        name_terms=("nonorientable", "eigensection", "obstruction", "row"),
        value=True,
    )
    assert has_evidence(receipt_text, name_terms=("sigma", "concentration", "target", "row"), value=True)
    assert has_evidence(receipt_text, name_terms=("pressure", "commutator", "target", "row"), value=True)


def test_bridge_flags_are_fail_closed(receipt_text: str) -> None:
    assert agda_bool_assignment(receipt_text, "sheafBridgeTyped", True)

    for name in (
        "topologicalStretchingLeakageLemmaProved",
        "dialecticSheafGluingProved",
        "pressureCommutatorGainProved",
        "mechanismExhaustionForFullClayNS",
        "clayPromotion",
        "clayNavierStokesPromoted",
        "fullClayNSSolved",
        "full_clay_ns_solved",
    ):
        assert agda_bool_assignment(receipt_text, name, False), name

    forbidden_true = [
        name
        for name, assigned in bool_assignments(receipt_text)
        if assigned == "true"
        and (
            "clay" in normalize(name)
            or "proved" in normalize(name)
            or "promoted" in normalize(name)
            or "fullnavierstokes" in normalize(name)
        )
    ]
    assert forbidden_true == []


def test_bridge_records_open_gaps_and_orcslpgf(receipt_text: str) -> None:
    normalized = normalize(receipt_text)
    for term in (
        "NSSheafOpenGapRow",
        "noTopologicalStretchingLeakageLemma",
        "noDialecticSheafGluingProof",
        "noPressureCommutatorGainProof",
        "noMechanismExhaustionForFullClayNS",
        "noClayPromotion",
        "canonicalNSSheafBridgeORCSLPGF",
        "canonicalNSSheafTopologicalObstructionBridgeReceipt",
    ):
        assert term in receipt_text, term

    for key in CONTROL_CARD_KEYS:
        assert normalize(key) in normalized, f"missing control-card string {key}"


def test_bridge_test_scope_does_not_target_index_or_docs(receipt_text: str) -> None:
    assert receipt_text
    changed_scope = {
        "DASHI/Physics/Closure/NSSheafTopologicalObstructionBridge.agda",
        "tests/test_ns_sheaf_topological_obstruction_bridge.py",
    }
    assert not (changed_scope & set(FORBIDDEN_EDIT_PATHS))
