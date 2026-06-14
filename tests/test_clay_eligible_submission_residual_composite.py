from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_PATH = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "ClayEligibleSubmissionResidualComposite.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.ClayEligibleSubmissionResidualComposite"


def read_boundary() -> str:
    assert AGDA_PATH.is_file(), AGDA_PATH.relative_to(REPO_ROOT).as_posix()
    return AGDA_PATH.read_text(encoding="utf-8")


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def bool_assignments(text: str) -> list[tuple[str, str]]:
    typed = re.findall(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b",
        text,
    )
    fields = re.findall(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*"
        r"(?:[A-Za-z][A-Za-z0-9_']*\s+)?"
        r"([A-Za-z][A-Za-z0-9_']*)\s*≡\s*(true|false)\b",
        text,
    )
    return typed + [(left + "_" + right, value) for left, right, value in fields]


def has_bool_evidence(text: str, terms: tuple[str, ...], value: bool) -> bool:
    expected = "true" if value else "false"
    normalized_terms = [normalize(term) for term in terms]
    for name, assigned in bool_assignments(text):
        normalized_name = normalize(name)
        if assigned == expected and all(term in normalized_name for term in normalized_terms):
            return True
    return False


def run_agda_no_libraries() -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "--no-libraries", str(AGDA_PATH.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_composite_typechecks_without_lane_imports() -> None:
    text = read_boundary()
    assert text.splitlines()[0] == f"module {MODULE_NAME} where"
    assert "import DASHI." not in text
    run_agda_no_libraries()


def test_composite_records_three_domains_and_zero_eligible_domains() -> None:
    text = read_boundary()
    normalized = normalize(text)

    for term in (
        "NS",
        "YM",
        "Paper8/UCT",
        "submissionDomainCountIs3",
        "domainCountIs3",
        "clayEligibleDomains = zero",
        "clayEligibleDomainsIsZero",
    ):
        assert normalize(term) in normalized, term


def test_composite_records_local_arithmetic_done_as_input_flag() -> None:
    text = read_boundary()
    normalized = normalize(text)

    assert has_bool_evidence(text, ("local", "arithmetic", "done"), True)
    assert normalize("existing sibling modules may supply it") in normalized
    assert normalize("recorded input flag") in normalized


def test_composite_records_ym_authority_packaging_as_next_state() -> None:
    text = read_boundary()
    normalized = normalize(text)

    for terms in (
        ("ym", "authority", "backed", "narrative", "ready"),
        ("ym", "authority", "packaging", "ready"),
        ("ym", "external", "acceptance", "pending"),
    ):
        assert has_bool_evidence(text, terms, True), terms

    for term in (
        "YM authority-backed narrative/posture is the next submission packaging state",
        "authority packaging ready",
        "external acceptance pending",
    ):
        assert normalize(term) in normalized, term


def test_composite_records_first_residual_labels() -> None:
    text = read_boundary()
    normalized = normalize(text)

    for term in (
        "NS-A theorem acceptance",
        "NS-A6 theorem acceptance",
        "NS pressure theorem still residual",
        "YM self-adjoint quotient",
        "YM external acceptance pending",
        "UCT.1 residual still deferred",
        "UCT.2 residual still deferred",
        "UCT.3 residual still deferred",
        "UCT.4 residual still deferred",
        "firstResidualCountIs9",
    ):
        assert normalize(term) in normalized, term


def test_composite_records_ns_pressure_and_uct_as_unpromoted_residuals() -> None:
    text = read_boundary()

    assert has_bool_evidence(text, ("ns", "pressure", "theorem", "still", "residual"), True)
    assert has_bool_evidence(text, ("uct", "residual", "still", "deferred"), True)


def test_composite_keeps_all_clay_and_terminal_promotion_false() -> None:
    text = read_boundary()

    for terms in (
        ("clay", "navier", "stokes", "promoted"),
        ("clay", "yang", "mills", "promoted"),
        ("paper8", "uct", "promoted"),
        ("terminal", "clay", "submission", "promoted"),
    ):
        assert has_bool_evidence(text, terms, False), terms

    forbidden_true_flags = [
        name
        for name, assigned in bool_assignments(text)
        if assigned == "true"
        and any(token in normalize(name) for token in ("clay", "terminal", "promoted"))
    ]
    assert forbidden_true_flags == []
