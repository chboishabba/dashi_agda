from __future__ import annotations

import re
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "YMAKingBochnerAuthorityBoundary.agda"
)


def read_source() -> str:
    return AGDA.read_text(encoding="utf-8")


def test_ym_a_king_bochner_authority_boundary_typechecks() -> None:
    subprocess.run(
        ["agda", "--no-libraries", str(AGDA.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=True,
    )


def test_ym_a_king_bochner_boundary_records_required_inputs() -> None:
    source = read_source()

    required_identifiers = (
        "king1986SpectralGapLowerBoundFormula",
        "kingAuthorityInputRecorded",
        "bochnerCasimirInputRecorded",
        "BochnerCasimirAdjointRow",
        "su2BochnerCasimirAdjointRow",
        "su3BochnerCasimirAdjointRow",
        "canonicalYMAKingBochnerAuthorityBoundary",
    )

    for identifier in required_identifiers:
        assert identifier in source

    assert "King 1986 authority input" in source
    assert "Delta_King(G,beta,L) >= c_King(G,beta,L) > 0" in source
    assert "C2(ad SU(2)) = 2" in source
    assert "C2(ad SU(3)) = 3" in source


def test_ym_a_king_bochner_boundary_keeps_promotions_false() -> None:
    source = read_source()

    false_flags = (
        "kingBoundTransportedToDashiDomain",
        "bochnerWeitzenbockProofInternalized",
        "ymATheoremPromoted",
        "clayYangMillsPromoted",
    )

    for flag in false_flags:
        assert re.search(rf"(?m)^{flag}\s*=\s*false$", source), flag
        assert f"{flag}IsFalse" in source or f"{flag[0].lower() + flag[1:]}IsFalse" in source

    assert "ymATheoremPromoted = true" not in source
    assert "clayYangMillsPromoted = true" not in source


def test_ym_a_king_bochner_boundary_does_not_claim_dashi_domain_theorem() -> None:
    source = read_source()

    assert "does not transport that lower bound to the DASHI domain theorem" in source
    assert "does not prove the DASHI domain theorem" not in source
    assert "DASHI domain theorem proved" not in source
    assert "DASHI domain theorem promoted" not in source
