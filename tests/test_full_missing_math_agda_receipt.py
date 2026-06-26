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
    / "FullMissingMathTheoremAgendaBoundary.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.FullMissingMathTheoremAgendaBoundary"


@pytest.fixture(scope="module")
def receipt_text() -> str:
    return RECEIPT.read_text(encoding="utf-8")


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*:\s*Bool\s*\n{name}\s*=\s*{expected}\b", text) is not None


def run_agda_no_libraries(path: Path) -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "--no-libraries", str(path.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_full_missing_math_agda_receipt_typechecks_standalone(receipt_text: str) -> None:
    assert f"module {MODULE_NAME}" in receipt_text
    run_agda_no_libraries(RECEIPT)


def test_receipt_records_exact_theorem_ids(receipt_text: str) -> None:
    for theorem_id in (
        "NS-A",
        "NS-B",
        "NS-C",
        "NS-D",
        "NS-E",
        "YM-A",
        "YM-B",
        "YM-C",
        "YM-D",
        "YM-E",
        "UCT-A",
        "UCT-B",
        "UCT-C",
        "UCT-D",
        "UCT-E",
        "UCT-F",
        "UCT-G",
        "UCT-H",
    ):
        assert theorem_id in receipt_text, theorem_id

    assert "fullMissingMathTheoremAgendaCountIs18" in receipt_text


def test_receipt_records_required_status_fields(receipt_text: str) -> None:
    for term in (
        "data AgendaStatus",
        "agendaOpen",
        "openStatus",
        "authorityIntake",
        "authorityIntakeStatus",
        "downstreamLocked",
        "downstreamLockedStatus",
        "record AgendaRow",
        "mkAuthorityIntakeRow YM-B",
        "mkAuthorityIntakeRow UCT-D",
    ):
        assert term in receipt_text, term


def test_receipt_records_exact_dependency_facts(receipt_text: str) -> None:
    for term in (
        "NS-C dependsOn NS-A",
        "NS-E dependsOn NS-A",
        "NS-E dependsOn NS-B",
        "NS-E dependsOn NS-C",
        "NS-E dependsOn NS-D",
        "YM-C dependsOn YM-B",
        "YM-D dependsOn YM-B",
        "UCT-E dependsOn UCT-D",
        "UCT-F dependsOn UCT-E",
        "UCT-G dependsOn UCT-F",
        "UCT-H dependsOn UCT-G",
        "UCT-E-H-depend-on-UCT-D-chain",
    ):
        assert term in receipt_text, term

    assert "fullMissingMathDependencyFactCountIs11" in receipt_text


def test_receipt_is_fail_closed_with_false_promotion_guards(receipt_text: str) -> None:
    assert agda_bool_assignment(receipt_text, "failClosed", True)

    for name in (
        "nsPromotionFlag",
        "ymPromotionFlag",
        "uctPromotionFlag",
        "anyTheoremPromotionFlag",
        "clayNavierStokesPromoted",
        "clayYangMillsPromoted",
        "unifiedClosureTheoremPromoted",
    ):
        assert agda_bool_assignment(receipt_text, name, False), name
        assert f"{name}IsFalse" in receipt_text


def test_receipt_contains_control_card_without_theorem_claim(receipt_text: str) -> None:
    normalized = normalize(receipt_text)
    for key in ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:"):
        assert normalize(key) in normalized, key

    assert "No proof, theorem discharge, or Clay promotion is claimed." in receipt_text
