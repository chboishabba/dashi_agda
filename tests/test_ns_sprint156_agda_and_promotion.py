from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
CLOSURE_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

CONTROL_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
SPRINT155_ANCHOR_SUPPORT_TERMS = (
    "Sprint155",
    "NSSprint155LocalizedEnstrophyIBPReceipt",
    "LocalizedEnstrophyIdentityAtScaleDelta",
    "BiotSavartNonlocalClosureAtScaleDelta",
    "SimultaneousConstantsCompatibility",
)
TRUE_WIDTH_MODEL_NAMES = (
    "ModelValidityForWidthODE",
    "ModelValidityForWidthODEProved",
)
FALSE_PROMOTION_NAMES = (
    "SymmetricHouLuoBKMFinite",
    "SymmetricHouLuoBKMFiniteProved",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "clayNavierStokesPromoted",
)
TRUE_PROMOTION_PATTERNS = (
    re.compile(
        r"\b(?:SymmetricHouLuoBKMFinite|SymmetricHouLuoBKMFiniteProved|"
        r"full_clay_ns_solved|fullClayNSSolved|clayNavierStokesPromoted)"
        r"\s*=\s*true\b"
    ),
    re.compile(
        r'"(?:symmetric_hou_luo_bkm_finite|bkm_finite|bkm_guard_closed|'
        r'full_clay_ns_solved|clay_navier_stokes_promoted|promotion_allowed|'
        r'clay_promotion_allowed)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
)


def normalize(value: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def sprint156_receipts() -> list[Path]:
    candidates = sorted(CLOSURE_DIR.glob("*Sprint156*.agda"))
    return [
        path
        for path in candidates
        if "receipt" in normalize(path.stem)
        and "sprint156" in normalize(path.read_text(encoding="utf-8", errors="replace"))
    ]


def sprint156_receipt() -> Path:
    receipt_candidates = sprint156_receipts()
    if not receipt_candidates:
        pytest.skip("Sprint156 Agda receipt is not present yet")
    if len(receipt_candidates) != 1:
        pytest.fail(
            "expected one Sprint156 Agda receipt, found "
            f"{[path.relative_to(REPO_ROOT).as_posix() for path in receipt_candidates]}"
        )
    return receipt_candidates[0]


@pytest.fixture(scope="module")
def receipt_text() -> tuple[Path, str]:
    receipt = sprint156_receipt()
    return receipt, receipt.read_text(encoding="utf-8")


def test_sprint156_receipt_exists_exactly_once() -> None:
    receipt_candidates = sprint156_receipts()
    assert receipt_candidates, "missing Sprint156 Agda receipt under DASHI/Physics/Closure"
    assert len(receipt_candidates) == 1, [
        path.relative_to(REPO_ROOT).as_posix() for path in receipt_candidates
    ]


def test_sprint156_receipt_typechecks_with_agda(receipt_text: tuple[Path, str]) -> None:
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


def test_sprint156_promotes_width_model_only(receipt_text: tuple[Path, str]) -> None:
    _, text = receipt_text

    for name in TRUE_WIDTH_MODEL_NAMES:
        assert agda_bool_assignment(text, name, True), name

    for name in FALSE_PROMOTION_NAMES:
        assert agda_bool_assignment(text, name, False), name

    for pattern in TRUE_PROMOTION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_sprint156_records_sprint155_anchor_support_and_control_card(
    receipt_text: tuple[Path, str],
) -> None:
    _, text = receipt_text
    normalized = normalize(text)

    missing_terms = [
        term for term in SPRINT155_ANCHOR_SUPPORT_TERMS if normalize(term) not in normalized
    ]
    assert not missing_terms, missing_terms

    assert re.search(
        r"\bSprint155\w*(?:Anchor|Support|Receipt|LocalizedEnstrophy|IBP)\w*\s*=\s*true\b",
        text,
    ), "missing true Sprint155 anchor/support assignment"

    for key in CONTROL_CARD_KEYS:
        assert re.search(rf'"{key}:\s', text), f"missing O/R/C/S/L/P/G/F string {key}:"


def test_sprint156_everything_import_once_when_wired(
    receipt_text: tuple[Path, str],
) -> None:
    receipt, _ = receipt_text
    assert EVERYTHING.is_file(), "DASHI/Everything.agda is not present"

    everything_text = EVERYTHING.read_text(encoding="utf-8")
    sprint156_imports = re.findall(
        r"^import\s+(DASHI\.Physics\.Closure\.[A-Za-z0-9_']*Sprint156[A-Za-z0-9_']*)\s*$",
        everything_text,
        flags=re.MULTILINE,
    )
    if not sprint156_imports:
        pytest.skip("Sprint156 receipt has not been wired into DASHI/Everything.agda yet")

    module_name = receipt.relative_to(REPO_ROOT).with_suffix("").as_posix().replace("/", ".")
    assert sprint156_imports == [module_name], sprint156_imports
