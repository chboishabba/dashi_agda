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
    / "NSSprint164MicrolocalTopologicalBridgeBoundaryReceipt.agda"
)
OBLIGATION_INDEX = REPO_ROOT / "DASHI" / "Promotion" / "ObligationIndex.agda"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

MODULE_NAME = (
    "DASHI.Physics.Closure."
    "NSSprint164MicrolocalTopologicalBridgeBoundaryReceipt"
)
RECEIPT_STEM = "NSSprint164MicrolocalTopologicalBridgeBoundaryReceipt"
CONTROL_CARD_KEYS = ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:")
REQUIRED_FALSE_FLAGS = (
    "MicrolocalAlignmentConcentrationLemma",
    "TopologicalStretchingLeakageLemma",
    "AngularDegeneracyPressureCommutatorGain",
    "FullLocalDefectMonotonicity",
    "MechanismExhaustionForFullClayNS",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "clayNavierStokesPromoted",
)
REQUIRED_TRUE_TARGET_FIELDS = (
    ("microlocal", "alignment", "concentration", "target", "recorded"),
    ("topological", "stretching", "leakage", "target", "recorded"),
    ("angular", "degeneracy", "pressure", "commutator", "gain", "target", "recorded"),
    ("degeneracy", "riding", "cascade", "target", "recorded"),
    ("sanni", "symbol", "level", "only", "anchor", "recorded"),
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


def has_named_bool_assignment(
    text: str,
    *,
    name_terms: tuple[str, ...],
    value: bool | None = None,
) -> bool:
    for name, assigned in bool_assignments(text):
        if value is not None and assigned != ("true" if value else "false"):
            continue
        normalized_name = normalize(name)
        if all(normalize(term) in normalized_name for term in name_terms):
            return True
    return False


def has_evidence(
    text: str,
    *,
    name_terms: tuple[str, ...],
    value: bool,
) -> bool:
    if has_named_bool_assignment(text, name_terms=name_terms, value=value):
        return True

    expected = "true" if value else "false"
    proof_decl = re.compile(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*"
        r"([A-Za-z][A-Za-z0-9_']*)\s*≡\s*"
        rf"{expected}\b"
    )
    for match in proof_decl.finditer(text):
        normalized_evidence = normalize(" ".join(match.groups()))
        if all(normalize(term) in normalized_evidence for term in name_terms):
            return True
    return False


@pytest.fixture(scope="module")
def receipt_text() -> str:
    if not RECEIPT.is_file():
        pytest.skip("Sprint164 Agda receipt has not landed yet")
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


def test_sprint164_receipt_typechecks_with_agda(receipt_text: str) -> None:
    assert receipt_text
    run_agda(RECEIPT)


def test_sprint164_receipt_records_microlocal_boundary(
    receipt_text: str,
) -> None:
    normalized = normalize(receipt_text)

    assert "Sprint164" in receipt_text
    assert "Sprint163" in receipt_text
    assert "MicrolocalTopologicalBridgeBoundary" in receipt_text
    assert RECEIPT_STEM in receipt_text

    assert has_evidence(
        receipt_text,
        name_terms=("Sprint163", "anchor"),
        value=True,
    ), "missing true Sprint163 anchor evidence"

    for terms in REQUIRED_TRUE_TARGET_FIELDS:
        assert has_evidence(
            receipt_text,
            name_terms=terms,
            value=True,
        ), f"missing true target-recorded evidence for {terms}"

    for term in (
        "MicrolocalVorticityDefectMeasure",
        "DegeneracySetSigma",
        "MaxEigenbundle",
        "NonOrientableMaxEigenbundle",
        "PressureFlux",
        "AlignmentDefect",
        "canonicalSprint164MicrolocalBoundaryRows",
        "sprint164MicrolocalBoundaryRowCount",
    ):
        assert term in receipt_text, term

    for key in CONTROL_CARD_KEYS:
        assert normalize(key) in normalized, f"missing O/R/C/S/L/P/G/F string {key}"


def test_sprint164_receipt_keeps_core_theorem_and_clay_flags_false(
    receipt_text: str,
) -> None:
    assert "Sprint164TheoremTargetRow" in receipt_text
    assert "canonicalSprint164TheoremTargetRows" in receipt_text
    assert "sprint164TheoremTargetRowCount" in receipt_text

    for terms in (
        ("microlocal", "alignment", "concentration", "lemma"),
        ("topological", "stretching", "leakage", "lemma"),
        ("angular", "degeneracy", "pressure", "commutator", "gain"),
        ("full", "local", "defect", "monotonicity"),
        ("mechanism", "exhaustion", "full", "clay"),
        ("full", "clay", "ns", "solved"),
        ("clay", "navier", "stokes", "promoted"),
    ):
        assert has_evidence(
            receipt_text,
            name_terms=terms,
            value=False,
        ), f"missing false theorem/Clay evidence for {terms}"

    for name in REQUIRED_FALSE_FLAGS:
        if name in receipt_text:
            assert agda_bool_assignment(receipt_text, name, False), name

    true_forbidden_flags = [
        name
        for name, assigned in bool_assignments(receipt_text)
        if assigned == "true"
        and (
            "clay" in normalize(name)
            or (
                "theorem" in normalize(name)
                and "target" not in normalize(name)
                and "recorded" not in normalize(name)
            )
            or "fullnavierstokes" in normalize(name)
            or (
                "lemma" in normalize(name)
                and "target" not in normalize(name)
                and "recorded" not in normalize(name)
            )
            or "monotonicity" in normalize(name)
        )
    ]
    assert true_forbidden_flags == []


def test_sprint164_obligation_index_integration_if_present(
    receipt_text: str,
) -> None:
    assert receipt_text
    assert OBLIGATION_INDEX.is_file(), "missing DASHI/Promotion/ObligationIndex.agda"
    text = OBLIGATION_INDEX.read_text(encoding="utf-8")
    if "Sprint164" not in text:
        pytest.skip("Sprint164 ObligationIndex integration has not landed yet")

    normalized = normalize(text)
    for term in (
        "Sprint164",
        "microlocal topological bridge boundary",
        RECEIPT_STEM,
        "FullClayExternalAuthorityBoundarySummary",
        "mkFullClayExternalAuthorityBoundarySummary",
        "promotesClay",
    ):
        assert normalize(term) in normalized, term
    assert MODULE_NAME in text
    assert re.search(r"\bpromotesClay\s*=\s*false\b", text)

    summary_rows = re.findall(
        r"\bmkFullClayExternalAuthorityBoundarySummary\b",
        text,
    )
    assert len(summary_rows) >= 6
    assert "canonicalUnifiedPromotionFullClayExternalAuthorityBoundaryCountIs6" in text
    assert re.search(
        r"canonicalUnifiedPromotionFullClayExternalAuthorityBoundaryCountIs6\s*:\s*"
        r"UnifiedPromotionObligationIndex\.fullClayExternalAuthorityBoundaryCount\s*"
        r"canonicalUnifiedPromotionObligationIndex\s*≡\s*6",
        text,
    )


def test_sprint164_everything_import_if_present(receipt_text: str) -> None:
    assert receipt_text
    assert EVERYTHING.is_file(), "missing DASHI/Everything.agda"
    text = EVERYTHING.read_text(encoding="utf-8")
    imports = re.findall(
        r"^import\s+"
        r"(DASHI\.Physics\.Closure\."
        r"NSSprint164MicrolocalTopologicalBridgeBoundaryReceipt)"
        r"\s*$",
        text,
        flags=re.MULTILINE,
    )
    if not imports:
        pytest.skip("Sprint164 Everything integration has not landed yet")
    assert imports == [MODULE_NAME]


def test_sprint164_integration_surfaces_typecheck_with_agda_if_present(
    receipt_text: str,
) -> None:
    assert receipt_text
    for path in (OBLIGATION_INDEX, EVERYTHING):
        text = path.read_text(encoding="utf-8")
        if "Sprint164" not in text:
            pytest.skip(f"Sprint164 integration has not landed in {path.name} yet")
    run_agda(OBLIGATION_INDEX)
    run_agda(EVERYTHING)
