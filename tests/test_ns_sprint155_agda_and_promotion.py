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
LOCALIZED_IDENTITY_NAMES = (
    "LocalizedEnstrophyIdentityAtScaleDelta",
    "LocalizedEnstrophyIdentityAtScaleDeltaProved",
    "localizedEnstrophyIdentityAtScaleDelta",
    "localizedEnstrophyIdentityAtScaleDeltaProved",
)
FALSE_GUARD_NAMES = (
    "SymmetricHouLuoBKMFinite",
    "SymmetricHouLuoBKMFiniteProved",
    "bkmFinite",
    "bkmGuardClosed",
    "BKMGuardClosed",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "clayNavierStokesPromoted",
    "clayPromotionAllowed",
    "promotionAllowed",
)
TRUE_BKM_CLAY_PATTERNS = (
    re.compile(
        r"\b(?:SymmetricHouLuoBKMFinite|SymmetricHouLuoBKMFiniteProved|"
        r"BKMGuardClosed|bkmGuardClosed|bkmFinite|full_clay_ns_solved|"
        r"fullClayNSSolved|clayNavierStokesPromoted|clayPromotionAllowed|"
        r"promotionAllowed)\s*=\s*true\b"
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


def sprint155_receipts() -> list[Path]:
    candidates = sorted(CLOSURE_DIR.glob("*Sprint155*.agda"))
    return [
        path
        for path in candidates
        if "receipt" in normalize(path.stem)
        and normalize(path.read_text(encoding="utf-8", errors="replace")).find("sprint155") >= 0
    ]


def sprint155_receipt() -> Path:
    receipt_candidates = sprint155_receipts()
    if not receipt_candidates:
        pytest.skip("Sprint155 Agda receipt is not present yet")
    if len(receipt_candidates) != 1:
        pytest.fail(
            "expected one Sprint155 Agda receipt, found "
            f"{[path.relative_to(REPO_ROOT).as_posix() for path in receipt_candidates]}"
        )
    return receipt_candidates[0]


@pytest.fixture(scope="module")
def receipt_text() -> tuple[Path, str]:
    receipt = sprint155_receipt()
    return receipt, receipt.read_text(encoding="utf-8")


def test_sprint155_receipt_exists() -> None:
    receipt_candidates = sprint155_receipts()
    assert receipt_candidates, "missing Sprint155 Agda receipt under DASHI/Physics/Closure"
    assert len(receipt_candidates) == 1, [
        path.relative_to(REPO_ROOT).as_posix() for path in receipt_candidates
    ]


def test_sprint155_receipt_typechecks_with_agda(receipt_text: tuple[Path, str]) -> None:
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


def test_sprint155_receipt_promotes_only_localized_identity(
    receipt_text: tuple[Path, str],
) -> None:
    _, text = receipt_text
    normalized = normalize(text)

    required_terms = [
        "Sprint155",
        "LocalizedEnstrophyIdentityAtScaleDelta",
        "Sprint154",
        "support",
        "closure",
        "guard",
        "Clay",
        "BKM",
    ]
    missing_terms = [term for term in required_terms if normalize(term) not in normalized]
    assert not missing_terms, missing_terms

    true_identity_names = [
        name for name in LOCALIZED_IDENTITY_NAMES if agda_bool_assignment(text, name, True)
    ]
    assert true_identity_names, "Sprint155 must set the localized identity gate to true"

    false_guard_names = [name for name in FALSE_GUARD_NAMES if agda_bool_assignment(text, name, False)]
    assert any("bkm" in normalize(name) for name in false_guard_names), false_guard_names
    assert any("clay" in normalize(name) or "promotion" in normalize(name) for name in false_guard_names), (
        false_guard_names
    )
    for pattern in TRUE_BKM_CLAY_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_sprint155_receipt_records_sprint154_support_and_control_card(
    receipt_text: tuple[Path, str],
) -> None:
    _, text = receipt_text

    assert re.search(
        r"\bSprint154\w*(?:Closure|Support)\w*\s*=\s*true\b",
        text,
    ), "missing true Sprint154 closure/support assignment"

    for key in CONTROL_CARD_KEYS:
        assert re.search(rf'"{key}:\s', text), f"missing O/R/C/S/L/P/G/F string {key}:"


def test_sprint155_everything_import_when_integration_is_present(
    receipt_text: tuple[Path, str],
) -> None:
    receipt, _ = receipt_text
    if not EVERYTHING.is_file():
        pytest.skip("DASHI/Everything.agda is not present")

    everything_text = EVERYTHING.read_text(encoding="utf-8")
    sprint155_imports = re.findall(
        r"^import\s+(DASHI\.Physics\.Closure\.[A-Za-z0-9_']*Sprint155[A-Za-z0-9_']*)\s*$",
        everything_text,
        flags=re.MULTILINE,
    )
    if not sprint155_imports:
        pytest.skip("Sprint155 receipt has not been wired into DASHI/Everything.agda yet")

    module_name = receipt.relative_to(REPO_ROOT).with_suffix("").as_posix().replace("/", ".")
    assert module_name in sprint155_imports, sprint155_imports
