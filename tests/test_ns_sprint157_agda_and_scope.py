from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
RECEIPT = REPO_ROOT / "DASHI/Physics/Closure/NSSprint157BKMIntegralContinuationReceipt.agda"
EVERYTHING = REPO_ROOT / "DASHI/Everything.agda"


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def test_sprint157_receipt_exists_and_typechecks() -> None:
    assert RECEIPT.is_file()
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")
    result = subprocess.run(
        [agda, str(RECEIPT.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_sprint157_promotes_symmetric_bkm_only() -> None:
    text = RECEIPT.read_text(encoding="utf-8")
    for name in (
        "BKMIntegralEstimate",
        "BKMIntegralEstimateProved",
        "ContinuationTheoremBridge",
        "ContinuationTheoremBridgeProved",
        "SymmetricHouLuoBKMFinite",
        "SymmetricHouLuoBKMFiniteProved",
    ):
        assert agda_bool_assignment(text, name, True), name

    for name in (
        "SymmetricHouLuoRegularityClassClosure",
        "MechanismExhaustionForFullClayNS",
        "full_clay_ns_solved",
        "fullClayNSSolved",
        "fullNavierStokesSolutionConstructed",
        "clayNavierStokesPromoted",
    ):
        assert agda_bool_assignment(text, name, False), name

    assert "NSSprint156ModelValidityForWidthODEReceipt" in text
    for key in ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:"):
        assert key in text


def test_sprint157_everything_import_once_when_wired() -> None:
    if not EVERYTHING.is_file():
        pytest.skip("DASHI/Everything.agda missing")
    text = EVERYTHING.read_text(encoding="utf-8")
    imports = re.findall(
        r"^import\s+(DASHI\.Physics\.Closure\.[A-Za-z0-9_']*Sprint157[A-Za-z0-9_']*)\s*$",
        text,
        flags=re.MULTILINE,
    )
    assert imports == ["DASHI.Physics.Closure.NSSprint157BKMIntegralContinuationReceipt"]
