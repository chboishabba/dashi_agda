from __future__ import annotations

import json
import re
import subprocess
import sys
import textwrap
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_finite_domination_candidate_audit.py"
SUMMARY_NAME = "ym_finite_domination_candidate_audit_summary.json"
REPORT_NAME = "ym_finite_domination_candidate_audit.md"


def write_fixture(repo_root: Path) -> None:
    closure = repo_root / "DASHI" / "Physics" / "Closure"
    closure.mkdir(parents=True, exist_ok=True)
    (closure / "YMBochnerWeitzenbockHamiltonianDominationBoundary.agda").write_text(
        textwrap.dedent(
            """\
            module DASHI.Physics.Closure.YMBochnerWeitzenbockHamiltonianDominationBoundary where

            open import Agda.Builtin.Bool using (Bool; false; true)
            open import Agda.Builtin.String using (String)

            clayYangMillsPromoted : Bool
            clayYangMillsPromoted = false

            bochnerWeitzenbockFiniteDominationRecorded : Bool
            bochnerWeitzenbockFiniteDominationRecorded = true

            finiteDominationText : String
            finiteDominationText =
              "Bochner-Weitzenbock candidate H_d on Omega-perp requires c1 Delta_YM,d and c2 Hol_d domination. Small-field c1 uses gamma and epsilon error absorption. Large-field Wilson holonomy c2 positivity remains open. Killing boundary and gauge quotient obligations remain downstream blockers."

            data Receipt : Set where
              recorded : Receipt
            """
        ),
        encoding="utf-8",
    )
    (closure / "YMLatticeMassGapAuthority.agda").write_text(
        textwrap.dedent(
            """\
            module DASHI.Physics.Closure.YMLatticeMassGapAuthority where

            open import Agda.Builtin.Bool using (Bool; false; true)
            open import Agda.Builtin.String using (String)

            balabanH3aIsLiveMissingContentFrontier : Bool
            balabanH3aIsLiveMissingContentFrontier = true

            h3aBalabanSeparationText : String
            h3aBalabanSeparationText =
              "H3a and Balaban remain downstream. Finite domination evidence does not close continuum transfer, no-spectral-pollution, OS/Wightman, or Clay Yang-Mills."

            data H3aReceipt : Set where
              recorded : H3aReceipt
            """
        ),
        encoding="utf-8",
    )


def run_script(repo_root: Path, out_dir: Path, markdown: bool = True) -> dict[str, Any]:
    cmd = [
        sys.executable,
        str(SCRIPT),
        "--repo-root",
        str(repo_root),
        "--out-dir",
        str(out_dir),
    ]
    if not markdown:
        cmd.append("--no-markdown")
    result = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode in (0, 1), result.stdout + result.stderr
    summary_path = out_dir / SUMMARY_NAME
    assert summary_path.exists(), result.stdout + result.stderr
    return json.loads(summary_path.read_text(encoding="utf-8"))


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [nested for child in value.values() for nested in flatten(child)]
    if isinstance(value, list):
        return [value] + [nested for child in value for nested in flatten(child)]
    return [value]


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def entries_with(summary: dict[str, Any], *terms: str) -> list[Any]:
    lowered = tuple(term.lower() for term in terms)
    return [
        item
        for item in flatten(summary)
        if all(term in json_text(item).lower() for term in lowered)
    ]


def test_finite_domination_audit_writes_json_and_optional_markdown(tmp_path: Path) -> None:
    write_fixture(tmp_path)
    out_dir = tmp_path / "out"

    summary = run_script(tmp_path, out_dir)

    assert (out_dir / SUMMARY_NAME).exists()
    assert (out_dir / REPORT_NAME).exists()
    assert summary["audit_id"] == "ym_finite_domination_candidate_audit"
    assert summary["route_decision"] == "fail-closed"
    assert summary["route_closed"] is False

    out_dir_no_md = tmp_path / "out-no-md"
    run_script(tmp_path, out_dir_no_md, markdown=False)
    assert (out_dir_no_md / SUMMARY_NAME).exists()
    assert not (out_dir_no_md / REPORT_NAME).exists()


def test_constants_formula_metadata_is_machine_checkable(tmp_path: Path) -> None:
    write_fixture(tmp_path)
    summary = run_script(tmp_path, tmp_path / "out")

    c1 = summary["constant_formula_metadata"]["small_field_c1"]
    assert c1["code"] == "BW-SF-c1"
    assert c1["coefficient"] == "c1"
    assert c1["formula"] == "c1 = gamma_d / 2 - C * epsilon"
    assert c1["strict_positivity_condition"] == "gamma_d / 2 - C * epsilon > 0"
    assert c1["equivalent_parameter_condition"] == "gamma_d > 2 * C * epsilon"
    assert c1["closed"] is False
    assert set(c1["required_parameters"]) == {"gamma_d", "C", "epsilon"}

    c2 = summary["constant_formula_metadata"]["large_field_c2"]
    assert c2["code"] == "BW-LF-c2"
    assert c2["coefficient"] == "c2"
    assert c2["strict_positivity_condition"] == "c2 > 0"
    assert c2["closed"] is False


def test_required_blockers_cover_boundary_gauge_h3a_balaban_and_c2(tmp_path: Path) -> None:
    write_fixture(tmp_path)
    summary = run_script(tmp_path, tmp_path / "out")
    text = json_text(summary)

    for code in (
        "BW-SF-c1",
        "BW-LF-c2",
        "KB-GQ-DOMAIN",
        "GQ-ZERO-MODE",
        "H3A-BALABAN-SEPARATION",
    ):
        rows = entries_with(summary, code)
        assert rows, code
        assert any(isinstance(row, dict) and row.get("blocked") is True for row in rows)

    for term in ("Killing", "gauge", "quotient", "H3a", "Balaban", "Wilson", "holonomy"):
        assert re.search(term, text, re.IGNORECASE)
    assert summary["blockers_closed"] is False


def test_promotion_flags_are_all_false_and_no_clay_ym_promotion_claim(tmp_path: Path) -> None:
    write_fixture(tmp_path)
    summary = run_script(tmp_path, tmp_path / "out")
    text = (tmp_path / "out" / REPORT_NAME).read_text(encoding="utf-8") + json_text(summary)

    assert summary["promotion_guard"]["never_claim_clay_or_ym_promotion"] is True
    assert summary["promotion_guard"]["closed"] is True
    assert all(value is False for value in summary["promotion_flags"].values())

    forbidden_true_patterns = (
        "clayYangMillsPromoted = true",
        '"clayYangMillsPromoted": true',
        "yangMillsPromoted = true",
        '"yangMillsPromoted": true',
        "continuumMassGapPromoted = true",
        '"continuumMassGapPromoted": true',
    )
    for pattern in forbidden_true_patterns:
        assert pattern not in text
