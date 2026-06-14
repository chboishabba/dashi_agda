from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "YMAAuthorityBackedSubmissionPathBoundary.agda"
)

TRUE_FLAGS = (
    "submissionPathRecorded",
    "finiteBTCellSelfAdjointnessDominationInternalTarget",
    "kingGammaDAuthorityIntakeRecorded",
    "balabanH3aRGAuthorityIntakeRecorded",
    "osWightmanAuthorityIntakeRecorded",
    "externalAcceptanceReviewRequired",
)

FALSE_FLAGS = (
    "clayEligibleWithoutExternalAuthority",
    "h3aInternalized",
    "ymClayPromoted",
    "terminalPromotion",
)

AUTHORITY_CHAIN_TERMS = (
    "finite BT self-adjointness/domination",
    "King supplies gamma_d authority intake",
    "Balaban H3a/RG",
    "OS/Wightman",
    "final external acceptance/review is required",
)

AUTHORITY_ROW_ORDER = (
    "finiteBTInternalTargetRow",
    "kingGammaDAuthorityRow",
    "balabanH3aRGAuthorityRow",
    "osWightmanAuthorityRow",
    "externalAcceptanceReviewRow",
)

BLOCKERS = (
    "H3a not internalized",
    "Clay eligibility without external authority false",
    "External acceptance/review still required",
    "YM Clay promotion false",
    "Terminal promotion false",
)


@pytest.fixture(scope="module")
def source() -> str:
    assert AGDA.is_file(), "missing YM-A authority-backed submission path boundary"
    return AGDA.read_text(encoding="utf-8")


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"(?m)^{re.escape(name)}\s*=\s*{expected}$", text) is not None


def test_ym_a_authority_backed_submission_path_boundary_typechecks(
    source: str,
) -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "--no-libraries", str(AGDA.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_submission_path_flags_record_path_but_no_external_free_clay(
    source: str,
) -> None:
    for name in TRUE_FLAGS:
        assert agda_bool_assignment(source, name, True), name
        assert not agda_bool_assignment(source, name, False), name
        assert f"{name}IsTrue" in source

    for name in FALSE_FLAGS:
        assert agda_bool_assignment(source, name, False), name
        assert not agda_bool_assignment(source, name, True), name
        assert f"{name}IsFalse" in source


def test_authority_chain_is_recorded_in_order_and_with_no_promotion(
    source: str,
) -> None:
    canonical_rows = re.search(
        r"canonicalAuthorityPathRows\s*:[\s\S]*?authorityPathRowCount\s*:",
        source,
    )
    assert canonical_rows is not None

    last_index = -1
    for row in AUTHORITY_ROW_ORDER:
        index = canonical_rows.group(0).find(row)
        assert index > last_index, row
        last_index = index

    for term in AUTHORITY_CHAIN_TERMS:
        assert term in source

    for constructor in (
        "internalFiniteBTTarget",
        "kingGammaD",
        "balabanH3aRG",
        "osWightman",
        "externalAcceptanceReview",
    ):
        assert constructor in source

    assert re.search(r"\bauthorityPathRowCountIs5\s*=\s*refl\b", source)
    assert "canonicalYMAAuthorityBackedSubmissionPathBoundary" in source


def test_boundary_blockers_keep_h3a_clay_and_terminal_false(source: str) -> None:
    for blocker in BLOCKERS:
        assert blocker in source

    assert re.search(r"\bsubmissionPathBlockerCountIs5\s*=\s*refl\b", source)
    assert "h3aInternalized = true" not in source
    assert "clayEligibleWithoutExternalAuthority = true" not in source
    assert "ymClayPromoted = true" not in source
    assert "terminalPromotion = true" not in source
    assert "ymClayPromotedFlagIsFalse" in source
    assert "terminalPromotionFlagIsFalse" in source
