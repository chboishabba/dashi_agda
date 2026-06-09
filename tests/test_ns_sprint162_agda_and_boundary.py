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
    / "NSSprint162CriticalResidualBoundaryReceipt.agda"
)
OBLIGATION_INDEX = REPO_ROOT / "DASHI" / "Promotion" / "ObligationIndex.agda"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

MODULE_NAME = (
    "DASHI.Physics.Closure.NSSprint162CriticalResidualBoundaryReceipt"
)
CONTROL_CARD_KEYS = ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:")
REQUIRED_CLAY_FALSE_FLAGS = (
    "fullClayNSSolved",
    "full_clay_ns_solved",
    "clayNavierStokesPromoted",
)
OPTIONAL_CLAY_FALSE_FLAGS = ("fullNavierStokesSolutionConstructed",)


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def has_named_bool_assignment(
    text: str,
    *,
    name_terms: tuple[str, ...],
    value: bool | None = None,
) -> bool:
    bool_decl = re.compile(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b"
    )
    for match in bool_decl.finditer(text):
        if value is not None and match.group(2) != ("true" if value else "false"):
            continue
        normalized_name = normalize(match.group(1))
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
        pytest.skip("Sprint162 Agda receipt has not landed yet")
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


def test_sprint162_receipt_typechecks_with_agda(receipt_text: str) -> None:
    assert receipt_text
    run_agda(RECEIPT)


def test_sprint162_receipt_records_critical_residual_boundary(
    receipt_text: str,
) -> None:
    normalized = normalize(receipt_text)

    assert "Sprint162" in receipt_text
    assert "Sprint161" in receipt_text
    assert "CriticalResidualBoundary" in receipt_text
    assert MODULE_NAME.rsplit(".", maxsplit=1)[-1] in receipt_text

    assert has_evidence(
        receipt_text,
        name_terms=("Sprint161", "anchor"),
        value=True,
    ), "missing true Sprint161 anchor evidence"
    assert has_evidence(
        receipt_text,
        name_terms=("critical", "residual", "boundary"),
        value=True,
    ), "missing true critical residual boundary evidence"

    for key in CONTROL_CARD_KEYS:
        assert normalize(key) in normalized, f"missing O/R/C/S/L/P/G/F string {key}"


def test_sprint162_receipt_keeps_residual_lane_fail_closed(
    receipt_text: str,
) -> None:
    assert has_evidence(
        receipt_text,
        name_terms=("persistent", "positive", "critical", "residual"),
        value=False,
    ), "persistent positive critical residual removal must remain false"
    assert has_evidence(
        receipt_text,
        name_terms=("pressure", "stretching", "depletion"),
        value=False,
    ), "pressure/stretching depletion lemma must remain false"
    assert has_evidence(
        receipt_text,
        name_terms=("mechanism", "exhaustion", "full", "clay"),
        value=False,
    ), "mechanism exhaustion must remain false"
    assert has_evidence(
        receipt_text,
        name_terms=("clay", "promotion"),
        value=False,
    ), "critical residual lane must not promote the Clay claim"

    for name in REQUIRED_CLAY_FALSE_FLAGS:
        assert agda_bool_assignment(receipt_text, name, False), name
    for name in OPTIONAL_CLAY_FALSE_FLAGS:
        if name in receipt_text:
            assert agda_bool_assignment(receipt_text, name, False), name

    assert not re.search(
        r"\b(?:fullClayNSSolved|full_clay_ns_solved|"
        r"fullNavierStokesSolutionConstructed|clayNavierStokesPromoted)"
        r"\s*=\s*true\b",
        receipt_text,
    )


def test_sprint162_obligation_index_integration_if_present(
    receipt_text: str,
) -> None:
    assert receipt_text
    assert OBLIGATION_INDEX.is_file(), "missing DASHI/Promotion/ObligationIndex.agda"
    text = OBLIGATION_INDEX.read_text(encoding="utf-8")
    if "Sprint162" not in text:
        pytest.skip("Sprint162 ObligationIndex integration has not landed yet")

    normalized = normalize(text)
    for term in (
        "Sprint162",
        "critical residual boundary",
        "NSSprint162CriticalResidualBoundaryReceipt",
        "promotesClay",
    ):
        assert normalize(term) in normalized, term
    assert MODULE_NAME in text
    assert re.search(r"\bpromotesClay\s*=\s*false\b", text)


def test_sprint162_everything_import_if_present(receipt_text: str) -> None:
    assert receipt_text
    assert EVERYTHING.is_file(), "missing DASHI/Everything.agda"
    text = EVERYTHING.read_text(encoding="utf-8")
    imports = re.findall(
        r"^import\s+"
        r"(DASHI\.Physics\.Closure\.NSSprint162CriticalResidualBoundaryReceipt)"
        r"\s*$",
        text,
        flags=re.MULTILINE,
    )
    if not imports:
        pytest.skip("Sprint162 Everything integration has not landed yet")
    assert imports == [MODULE_NAME]


def test_sprint162_integration_surfaces_typecheck_with_agda_if_present(
    receipt_text: str,
) -> None:
    assert receipt_text
    for path in (OBLIGATION_INDEX, EVERYTHING):
        text = path.read_text(encoding="utf-8")
        if "Sprint162" not in text:
            pytest.skip(f"Sprint162 integration has not landed in {path.name} yet")
    run_agda(OBLIGATION_INDEX)
    run_agda(EVERYTHING)
