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
    / "NSPointwiseToAbelAuthorityReductionBoundary.agda"
)


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def bool_assignments(text: str) -> list[tuple[str, str]]:
    return re.findall(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b",
        text,
    )


def has_bool(text: str, terms: tuple[str, ...], value: bool) -> bool:
    expected = "true" if value else "false"
    for name, assigned in bool_assignments(text):
        if assigned != expected:
            continue
        normalized = normalize(name)
        if all(normalize(term) in normalized for term in terms):
            return True
    proof = re.compile(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*"
        r"([A-Za-z][A-Za-z0-9_']*)\s*≡\s*"
        rf"{expected}\b"
    )
    for match in proof.finditer(text):
        normalized = normalize(" ".join(match.groups()))
        if all(normalize(term) in normalized for term in terms):
            return True
    return False


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), "missing NS pointwise-to-Abel authority boundary"
    return RECEIPT.read_text(encoding="utf-8")


def run_agda(path: Path) -> None:
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
    output = result.stdout + result.stderr
    assert result.returncode == 0, output


def test_authority_reduction_boundary_typechecks(receipt_text: str) -> None:
    assert "NSPointwiseToAbelAuthorityReductionBoundary" in receipt_text
    run_agda(RECEIPT)


def test_authority_reduction_records_required_route_flags(
    receipt_text: str,
) -> None:
    normalized = normalize(receipt_text)
    for term in (
        "diagonal same-shell stretching",
        "Coifman-Meyer absorption",
        "localization / pressure commutator",
        "harmonic pressure tail",
        "Abel shell-mixing LLN downstream of A3",
        "A3 stationarity",
        "AuthorityReductionRouteFlag",
        "canonicalAuthorityReductionRouteFlags",
        "authorityReductionRouteFlagCountIs8",
    ):
        assert normalize(term) in normalized, term

    for terms in (
        ("diagonal", "same", "shell", "recorded"),
        ("off", "diagonal", "coifman", "meyer", "recorded"),
        ("localization", "pressure", "commutator", "recorded"),
        ("harmonic", "tail", "recorded"),
        ("abel", "shell", "mixing", "lln", "a3", "recorded"),
        ("authority", "reduction", "route", "recorded"),
    ):
        assert has_bool(receipt_text, terms, True), terms


def test_authority_reduction_keeps_promotions_false(
    receipt_text: str,
) -> None:
    for terms in (
        ("a6", "transfer", "promoted"),
        ("ns", "clay", "promoted"),
        ("terminal", "promotion"),
        ("terminal", "unification", "promoted"),
    ):
        assert has_bool(receipt_text, terms, False), terms

    true_forbidden = [
        name
        for name, assigned in bool_assignments(receipt_text)
        if assigned == "true"
        and (
            "a6transferpromoted" in normalize(name)
            or "nsclaypromoted" in normalize(name)
            or "terminalpromotion" in normalize(name)
            or "terminalunificationpromoted" in normalize(name)
        )
    ]
    assert true_forbidden == []


def test_authority_reduction_exposes_control_summary(
    receipt_text: str,
) -> None:
    normalized = normalize(receipt_text)
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        assert normalize(f"{key} ") in normalized
    assert "orcsLpgfSummary" in receipt_text
