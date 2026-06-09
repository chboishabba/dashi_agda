from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
CLOSURE_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
OBLIGATION_INDEX = REPO_ROOT / "DASHI" / "Promotion" / "ObligationIndex.agda"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

BLOCKER_FALSE_OPEN_FLAGS = (
    "MechanismExhaustionForFullClayNS",
    "GeneralDataReductionToCriticalProfiles",
    "CriticalProfileCompactnessForNS",
    "AxisymmetricOrSymmetricReductionExclusion",
    "NonAxisymmetricVortexStretchingControl",
    "PressureNonlocalityClosureForGeneralData",
    "CriticalNormExhaustionCriterion",
    "FullNavierStokesContinuationBridge",
    "ClaySubmissionPromotionPacket",
)
CLAY_FALSE_FLAGS = (
    "fullClayNSSolved",
    "full_clay_ns_solved",
    "fullNavierStokesSolutionConstructed",
    "clayNavierStokesPromoted",
)
CLAY_OPEN_FLAGS = (
    "fullClayNSSolvedOpen",
    "fullClayNSSolvedSnakeOpenFlag",
    "fullNavierStokesSolutionConstructedOpen",
    "clayNavierStokesPromotedOpen",
)
CONTROL_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def has_named_bool_assignment(
    text: str,
    *,
    name_terms: tuple[str, ...],
    value: bool,
) -> bool:
    expected = "true" if value else "false"
    for match in re.finditer(r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b", text):
        if match.group(2) != expected:
            continue
        normalized_name = normalize(match.group(1))
        if all(normalize(term) in normalized_name for term in name_terms):
            return True
    return False


def sprint159_receipts() -> list[Path]:
    return sorted(
        path
        for path in CLOSURE_DIR.glob("*Sprint159*.agda")
        if "receipt" in normalize(path.stem)
    )


@pytest.fixture(scope="module")
def receipt_text() -> tuple[Path, str]:
    receipts = sprint159_receipts()
    assert receipts, "missing Sprint159 Agda receipt under DASHI/Physics/Closure"
    assert len(receipts) == 1, [
        path.relative_to(REPO_ROOT).as_posix() for path in receipts
    ]
    receipt = receipts[0]
    return receipt, receipt.read_text(encoding="utf-8")


def test_sprint159_receipt_typechecks_with_agda(
    receipt_text: tuple[Path, str],
) -> None:
    receipt, _ = receipt_text
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, str(receipt.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_sprint159_external_authority_boundary_and_sprint158_anchor(
    receipt_text: tuple[Path, str],
) -> None:
    _, text = receipt_text
    normalized = normalize(text)

    assert agda_bool_assignment(text, "ExternalAuthorityBoundary", True)
    assert "Sprint158" in text
    assert "NSSprint158SymmetricHouLuoRegularityClassClosureReceipt" in text
    assert "SymmetricHouLuoRegularityClassClosure" in text
    assert has_named_bool_assignment(
        text,
        name_terms=("Sprint158", "Support"),
        value=True,
    ), "missing true Sprint158 support flag"
    assert "sprint158SymmetricClosureAnchor" in text
    assert "sprint159AnchorsSprint158SymmetricClosure" in text
    assert re.search(
        r"sprint159AnchorsSprint158SymmetricClosure\s*:\s*"
        r"sprint158SymmetricClosureAnchor\s*≡\s*true",
        text,
    ), "missing true Sprint158 anchor proof"

    for key in CONTROL_CARD_KEYS:
        assert normalize(f"{key}:") in normalized, f"missing O/R/C/S/L/P/G/F string {key}:"


def test_sprint159_blockers_open_and_clay_flags_fail_closed(
    receipt_text: tuple[Path, str],
) -> None:
    _, text = receipt_text

    for name in BLOCKER_FALSE_OPEN_FLAGS:
        assert agda_bool_assignment(text, name, False), name
        assert agda_bool_assignment(text, f"{name}Open", True), f"{name}Open"

    for name in CLAY_FALSE_FLAGS:
        assert agda_bool_assignment(text, name, False), name
    for name in CLAY_OPEN_FLAGS:
        assert agda_bool_assignment(text, name, True), name

    assert not re.search(
        r"\b(?:fullClayNSSolved|full_clay_ns_solved|fullNavierStokesSolutionConstructed|"
        r"clayNavierStokesPromoted)\s*=\s*true\b",
        text,
    )


def test_sprint159_obligation_index_external_authority_summary_layer(
    receipt_text: tuple[Path, str],
) -> None:
    receipt, _ = receipt_text
    assert OBLIGATION_INDEX.is_file(), "missing DASHI/Promotion/ObligationIndex.agda"
    text = OBLIGATION_INDEX.read_text(encoding="utf-8")
    normalized = normalize(text)
    module_name = receipt.relative_to(REPO_ROOT).with_suffix("").as_posix().replace("/", ".")

    for term in (
        "Sprint159",
        "external authority",
        "FullClayExternalAuthorityBoundarySummary",
        "FullClayExternalAuthorityBoundaryLane",
        "mkFullClayExternalAuthorityBoundarySummary",
        "promotesClay",
    ):
        assert normalize(term) in normalized, term
    assert module_name in text
    assert re.search(r"\bpromotesClay\s*=\s*false\b", text)


def test_sprint159_everything_imports_new_receipt_once(
    receipt_text: tuple[Path, str],
) -> None:
    receipt, _ = receipt_text
    assert EVERYTHING.is_file(), "missing DASHI/Everything.agda"
    text = EVERYTHING.read_text(encoding="utf-8")
    module_name = receipt.relative_to(REPO_ROOT).with_suffix("").as_posix().replace("/", ".")
    imports = re.findall(
        r"^import\s+(DASHI\.Physics\.Closure\.[A-Za-z0-9_']*Sprint159[A-Za-z0-9_']*)\s*$",
        text,
        flags=re.MULTILINE,
    )
    assert imports == [module_name]
