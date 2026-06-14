from __future__ import annotations

import json
import re
import subprocess
import sys
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_CANDIDATES = (
    REPO_ROOT / "scripts" / "ym_option_b_gap_audit.py",
    REPO_ROOT / "scripts" / "ym_option_b_gap_audit_harness.py",
    REPO_ROOT / "scripts" / "ym_paper3_option_b_gap_audit.py",
)

B_STEPS = ("B1", "B2", "B3", "B4", "B5")
FAIL_CLOSED_WORDS = ("fail", "closed")
NON_PROMOTION_WORDS = ("promotion", "false")
OPTION_B_WORDS = ("option", "b")
POLYMER_WORDS = ("polymer",)


def script_path() -> Path:
    for path in SCRIPT_CANDIDATES:
        if path.exists():
            return path
    pytest.skip("Option-B gap audit script is not integrated yet")


def write_option_b_fixture(repo_root: Path, *, all_closed: bool = False) -> None:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    paper_dir = repo_root / "Docs" / "papers" / "live"
    paper_dir.mkdir(parents=True, exist_ok=True)
    manifest_dir = repo_root / "Docs" / "papers" / "generated"
    manifest_dir.mkdir(parents=True, exist_ok=True)
    false_value = "true" if all_closed else "false"
    (module_dir / "OptionBNativePolymerFiveLemmaBoundaryReceipt.agda").write_text(
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.OptionBNativePolymerFiveLemmaBoundaryReceipt where

            open import Agda.Builtin.Bool using (Bool; false; true)
            open import Agda.Builtin.String using (String)

            clayYangMillsPromoted : Bool
            clayYangMillsPromoted = false

            optionBTerminalPromotion : Bool
            optionBTerminalPromotion = false

            optionBGapAuditB1Closed : Bool
            optionBGapAuditB1Closed = true

            optionBGapAuditB2Closed : Bool
            optionBGapAuditB2Closed = {false_value}

            optionBGapAuditB3Closed : Bool
            optionBGapAuditB3Closed = {false_value}

            optionBGapAuditB4Closed : Bool
            optionBGapAuditB4Closed = {false_value}

            optionBGapAuditB5Closed : Bool
            optionBGapAuditB5Closed = {false_value}

            optionBGapAuditSurface : String
            optionBGapAuditSurface =
              "Option B B1 polymer activity B2 KP summability B3 infinite volume B4 transfer domination B5 continuum mass gap; fail closed, no terminal promotion"

            data OptionBGapAuditReceipt : Set where
              recorded :
                OptionBGapAuditReceipt
            """
        ),
        encoding="utf-8",
    )
    (module_dir / "YMBalabanOptionATheoremIntakeReceipt.agda").write_text(
        "module DASHI.Physics.Closure.YMBalabanOptionATheoremIntakeReceipt where\n"
        "-- Option A Balaban theorem intake remains external and non-promotional.\n",
        encoding="utf-8",
    )
    (paper_dir / "Paper3YangMillsClayDraft.md").write_text(
        "Option-B companion path records B1 Casimir suppression, B2 polymer localization, "
        "B3 KP activity, B4 trace-norm consequence, and B5 intermediate-beta RG induction. "
        "It is fail closed with no Clay promotion.\n",
        encoding="utf-8",
    )
    manifest_rows = [
        {
            "paper": "Paper3 YM",
            "lemma": f"Option B {step} fixture boundary",
            "agda_file": "DASHI/Physics/Closure/OptionBNativePolymerFiveLemmaBoundaryReceipt.agda",
            "exact_var": f"{step}Fixture",
            "expected_status": "false" if step in {"B3", "B5"} else "diagnostic",
            "authority": "repo-native Option-B fixture",
            "section": "fixture",
            "governance_note": f"{step} remains blocked and cannot promote Clay YM.",
        }
        for step in B_STEPS
    ]
    (manifest_dir / "core_papers_theorem_var_manifest.json").write_text(
        json.dumps({"rows": manifest_rows}),
        encoding="utf-8",
    )


def run_audit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    proc = subprocess.run(
        [
            sys.executable,
            str(script_path()),
            "--repo-root",
            str(repo_root),
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode in (0, 1), proc.stdout + proc.stderr
    return json.loads(proc.stdout)


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [nested for item in value.values() for nested in flatten(item)]
    if isinstance(value, list):
        return [value] + [nested for item in value for nested in flatten(item)]
    return [value]


def words(value: Any) -> set[str]:
    found = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(found):
        if word.startswith("promot"):
            found.add("promotion")
        if word.startswith("poly"):
            found.add("polymer")
    return found


def matching_items(value: Any, required: tuple[str, ...]) -> list[Any]:
    return [item for item in flatten(value) if all(word in words(item) for word in required)]


def bool_values_by_name(value: Any) -> dict[str, bool]:
    values: dict[str, bool] = {}
    for item in flatten(value):
        if isinstance(item, dict):
            name = item.get("name") or item.get("id") or item.get("gate") or item.get("step")
            current = item.get("value")
            if isinstance(name, str) and isinstance(current, bool):
                values[name] = current
    return values


def is_actual_promotion_flag(name: str) -> bool:
    lower = name.lower()
    if "block_promotion" in lower or "blocks_promotion" in lower:
        return False
    return (
        lower == "promotion_allowed"
        or lower == "clay_promotion"
        or "promoted" in lower
        or "terminalpromotion" in lower
        or "terminal_promotion" in lower
    )


def assert_option_b_summary_is_fail_closed(summary: dict[str, Any]) -> None:
    serialized = json.dumps(summary, sort_keys=True).lower()

    for step in B_STEPS:
        assert step.lower() in serialized
    assert matching_items(summary, OPTION_B_WORDS)
    assert matching_items(summary, POLYMER_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    assert matching_items(summary, NON_PROMOTION_WORDS) or "promoted" in serialized and "false" in serialized

    named_bools = bool_values_by_name(summary)
    promotion_bools = {
        name: value
        for name, value in named_bools.items()
        if is_actual_promotion_flag(name)
    }
    top_level_promotion = {
        key: value
        for key, value in summary.items()
        if isinstance(value, bool) and is_actual_promotion_flag(key)
    }
    assert promotion_bools or top_level_promotion
    assert all(value is False for value in {**promotion_bools, **top_level_promotion}.values())


def test_option_b_fixture_audit_records_b1_b5_and_fails_closed(tmp_path: Path) -> None:
    write_option_b_fixture(tmp_path)

    summary = run_audit(tmp_path, tmp_path / "out")

    assert_option_b_summary_is_fail_closed(summary)


def test_option_b_real_audit_does_not_promote_current_paper3_surface(tmp_path: Path) -> None:
    summary = run_audit(REPO_ROOT, tmp_path / "out")

    assert_option_b_summary_is_fail_closed(summary)
