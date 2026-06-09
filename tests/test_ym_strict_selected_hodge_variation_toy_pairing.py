from __future__ import annotations

import re
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_FILE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "YMStrictSelectedHodgeVariationToyPairing.agda"
)
MODULE = "DASHI.Physics.Closure.YMStrictSelectedHodgeVariationToyPairing"


def read_source() -> str:
    assert AGDA_FILE.is_file(), "missing " + str(AGDA_FILE.relative_to(REPO_ROOT))
    return AGDA_FILE.read_text(encoding="utf-8")


def test_toy_pairing_surface_has_non_vacuous_carriers_and_receipt() -> None:
    source = read_source()

    assert "data ToyVariation" in source
    assert "toyVariationZero" in source
    assert "toyVariationElectric" in source
    assert "toyVariationMagnetic" in source
    assert "data ToyActionScalar" in source
    assert "toyActionZero" in source
    assert "toyActionPositive" in source
    assert "toyActionNegative" in source
    assert "toyPairing :" in source
    assert "toyPairing toyVariationElectric toyActionZero =" in source
    assert "toyReferencePairingIsPositive" in source
    assert "toyReferencePairingIsNonzero" in source
    assert re.search(r"toyReferencePairingIsPositive\s*=\s*refl", source)
    assert re.search(r"toyReferencePairingIsNonzero\s*=\s*refl", source)
    assert "canonicalToySelectedHodgeVariationPairingReceipt" in source


def test_toy_pairing_surface_keeps_real_hodge_and_promotion_flags_closed() -> None:
    source = read_source()

    required_terms = [
        "missingVariationPairingForSelectedHodgeStarRemainsTrue",
        "missingVariationPairingForSelectedHodgeStarRemainsTrueIsTrue",
        "BTFiniteHodgeVariationTheorem",
        "BTFiniteHodgeVariationTheoremIsFalse",
        "continuumMassGapPromoted",
        "continuumMassGapPromotedIsFalse",
        "clayYangMillsPromoted",
        "clayYangMillsPromotedIsFalse",
        "realSelectedHodgeBlockerIsStillMissingVariationPairing",
    ]
    for term in required_terms:
        assert term in source

    assert re.search(r"BTFiniteHodgeVariationTheorem\s*=\s*false", source)
    assert re.search(r"continuumMassGapPromoted\s*=\s*false", source)
    assert re.search(r"clayYangMillsPromoted\s*=\s*false", source)
    assert "YMObs.missingVariationPairingForSelectedHodgeStar" in source
    assert "This receipt closes only a tiny finite toy pairing" in source


def test_toy_pairing_surface_has_no_unchecked_agda_markers() -> None:
    source = read_source()
    forbidden = [
        "post" + "ulate",
        "{!",
        "!}",
        "primTrustMe",
        "{-# TERMINATING #-}",
        "{-# NON_TERMINATING #-}",
    ]
    for marker in forbidden:
        assert marker not in source


def test_toy_pairing_surface_typechecks_standalone() -> None:
    result = subprocess.run(
        ["agda", str(AGDA_FILE.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    assert MODULE.replace(".", "/") in str(AGDA_FILE)
