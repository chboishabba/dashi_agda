from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_FILE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "UniformProjectionNonlocalityGapFinite.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.UniformProjectionNonlocalityGapFinite"


def read_text() -> str:
    assert AGDA_FILE.is_file(), f"missing {AGDA_FILE.relative_to(REPO_ROOT)}"
    return AGDA_FILE.read_text(encoding="utf-8")


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def run_agda() -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, str(AGDA_FILE.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def bool_assignments(text: str) -> dict[str, str]:
    return dict(
        re.findall(
            r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b",
            text,
        )
    )


def function_nat_values(text: str, function_name: str) -> dict[str, int]:
    pattern = re.compile(
        rf"\b{re.escape(function_name)}\s+"
        r"(nsRankOne|ymBTp2|ymBTp3)\s*=\s*\n\s*([0-9]+)\b"
    )
    return {domain: int(value) for domain, value in pattern.findall(text)}


def test_uniform_projection_nonlocality_gap_module_typechecks() -> None:
    text = read_text()
    assert text.splitlines()[0] == f"module {MODULE_NAME} where"
    run_agda()


def test_uniform_projection_nonlocality_gap_has_required_domains_and_values() -> None:
    text = read_text()
    normalized = normalize(text)

    for domain in ("nsRankOne", "ymBTp2", "ymBTp3"):
        assert normalize(domain) in normalized
        assert f'"{domain}"' in text

    assert function_nat_values(text, "gapNumerator") == {
        "nsRankOne": 1,
        "ymBTp2": 1,
        "ymBTp3": 2,
    }
    assert function_nat_values(text, "gapDenominator") == {
        "nsRankOne": 2,
        "ymBTp2": 4,
        "ymBTp3": 9,
    }

    for proof_name in (
        "nsRankOneGapNumeratorIsOne",
        "nsRankOneGapDenominatorIsTwo",
        "ymBTp2GapNumeratorIsOne",
        "ymBTp2GapDenominatorIsFour",
        "ymBTp3GapNumeratorIsTwo",
        "ymBTp3GapDenominatorIsNine",
    ):
        assert proof_name in text


def test_uniform_projection_nonlocality_gap_status_flags_are_fail_closed() -> None:
    flags = bool_assignments(read_text())
    assert flags["finiteUniformProjectionNonlocalityGap"] == "true"
    assert flags["continuumUniformProjectionNonlocalityGap"] == "false"
    assert flags["semanticUnificationPromoted"] == "false"
    assert flags["clayYangMillsPromoted"] == "false"
    assert flags["clayNavierStokesPromoted"] == "false"


def test_uniform_projection_nonlocality_gap_nonzero_samples_and_no_holes() -> None:
    text = read_text()
    for sample in (
        "nsRankOneOffDiagonalLeakage",
        "ymBTp2HodgeDefect",
        "ymBTp3HodgeDefect",
    ):
        assert sample in text

    for control_key in ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:"):
        assert control_key in text

    forbidden = ("postulate", "{!!}", "?", "TODO", "skeleton")
    lowered = text.lower()
    for token in forbidden:
        if token == "?":
            assert "?" not in text
        else:
            assert token.lower() not in lowered
