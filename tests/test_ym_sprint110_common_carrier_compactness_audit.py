from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint110_common_carrier_compactness_audit.py"
SUMMARY_NAME = "ym_sprint110_common_carrier_compactness_audit_summary.json"
REPORT_NAME = "ym_sprint110_common_carrier_compactness_audit.md"
MODULE_GLOBS = ("YMSprint109*.agda", "YMSprint110*.agda")

FORBIDDEN_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
    "{" + "!",
    "!" + "}",
)
FORBIDDEN_PROMOTION = "clayYangMillsPromoted = " + "true"
FORBIDDEN_WORD_PATTERNS = {
    "post" + "ulate": re.compile(r"\bpost" + "ulate\b"),
    "TO" + "DO": re.compile(r"\bTO" + "DO\b"),
    "stu" + "b": re.compile(r"\bstu" + "b\b", re.IGNORECASE),
}

COMMON_CARRIER_WORDS = ("common", "carrier")
WEAK_COMPACTNESS_WORDS = ("weak", "compactness")
LOWER_SEMICONTINUITY_WORDS = ("lower", "semicontinuity")
RECOVERY_LIMSUP_WORDS = ("recovery", "limsup")
BOTTOM_THRESHOLD_WORDS = ("bottom", "threshold")
FAIL_CLOSED_WORDS = ("fail", "closed")


def run_script(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    result = subprocess.run(
        [
            "python",
            str(SCRIPT),
            "--repo-root",
            str(repo_root),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode in (0, 1), result.stderr

    summary_path = out_dir / SUMMARY_NAME
    assert summary_path.exists(), result.stdout + result.stderr
    return json.loads(summary_path.read_text())


def write_sprint_module(repo_root: Path, sprint: int, name: str, text: str) -> Path:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    path = module_dir / f"YMSprint{sprint}{name}.agda"
    path.write_text(text)
    return path


def sprint110_fixture_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint110CommonCarrierCompactnessAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        commonCarrierConstructedHere : Bool
        commonCarrierConstructedHere = false

        weakCompactnessTheoremProved : Bool
        weakCompactnessTheoremProved = false

        closedFormLowerSemicontinuityTheoremProved : Bool
        closedFormLowerSemicontinuityTheoremProved = false

        recoveryCoreDensityEnergyLimsupTheoremProved : Bool
        recoveryCoreDensityEnergyLimsupTheoremProved = false

        bottomSectorThresholdNoCollapseTheoremProved : Bool
        bottomSectorThresholdNoCollapseTheoremProved = false

        commonCarrierEvidenceText : String
        commonCarrierEvidenceText =
          "common carrier evidence identifies one physical Hilbert carrier and compatible embeddings"

        weakCompactnessEvidenceText : String
        weakCompactnessEvidenceText =
          "weak compactness evidence extracts subsequences from normalized finite-energy transfer-form states"

        closedFormLowerSemicontinuityEvidenceText : String
        closedFormLowerSemicontinuityEvidenceText =
          "closed-form lower semicontinuity evidence gives Mosco liminf control for the quadratic form"

        recoveryCoreDensityEnergyLimsupEvidenceText : String
        recoveryCoreDensityEnergyLimsupEvidenceText =
          "recovery core density and energy limsup evidence records approximants without increasing limiting form energy"

        bottomSectorThresholdNoCollapseEvidenceText : String
        bottomSectorThresholdNoCollapseEvidenceText =
          "bottom sector threshold no-collapse evidence separates the vacuum projection from the first threshold"

        data CommonCarrierCompactnessReceipt : Set where
          recorded :
            CommonCarrierCompactnessReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("semicont"):
            words.add("semicontinuity")
        if word.startswith("compact"):
            words.add("compactness")
        if word.startswith("recover"):
            words.add("recovery")
        if word.startswith("collaps"):
            words.add("collapse")
        if word.startswith("limsup"):
            words.add("limsup")
        if word.startswith("threshold"):
            words.add("threshold")
    return words


def flatten_values(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [nested for item in value.values() for nested in flatten_values(item)]
    if isinstance(value, list):
        return [value] + [nested for item in value for nested in flatten_values(item)]
    return [value]


def matching_items(value: Any, phrase: tuple[str, ...]) -> list[Any]:
    return [
        item
        for item in flatten_values(value)
        if all(word in normalized_words(item) for word in phrase)
    ]


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def assert_summary_records_common_carrier_compactness_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, COMMON_CARRIER_WORDS)
    assert matching_items(summary, WEAK_COMPACTNESS_WORDS)
    assert matching_items(summary, LOWER_SEMICONTINUITY_WORDS)
    assert matching_items(summary, RECOVERY_LIMSUP_WORDS)
    assert matching_items(summary, BOTTOM_THRESHOLD_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    assert summary["required_common_carrier_compactness_theorem_flags"]
    assert not all(
        flag["value"] is True
        for flag in summary["required_common_carrier_compactness_theorem_flags"]
    )


def has_empty_data_declaration(text: str) -> bool:
    lines = text.splitlines()
    for index, line in enumerate(lines):
        if not re.match(r"^data\s+\S+.*\bwhere\s*$", line):
            continue

        saw_constructor = False
        for following in lines[index + 1 :]:
            stripped = following.strip()
            if not stripped or stripped.startswith("--"):
                continue
            if not following.startswith((" ", "\t")):
                break
            saw_constructor = True
            break
        if not saw_constructor:
            return True
    return False


def sprint109_110_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint110_fixture_summary_records_common_carrier_compactness_audit(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 110, "CommonCarrierCompactnessAuditFixture", sprint110_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_common_carrier_compactness_audit(summary)
    assert summary["scanned_surfaces"]["sprint110"] == [
        "DASHI/Physics/Closure/YMSprint110CommonCarrierCompactnessAuditFixture.agda"
    ]


def test_sprint110_real_summary_records_fail_closed_common_carrier_compactness_audit(
    tmp_path: Path,
) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["scanned_surfaces"]["sprint109"]
    assert matching_items(summary, COMMON_CARRIER_WORDS)
    assert matching_items(summary, WEAK_COMPACTNESS_WORDS)
    assert matching_items(summary, LOWER_SEMICONTINUITY_WORDS)
    assert matching_items(summary, RECOVERY_LIMSUP_WORDS)
    assert matching_items(summary, BOTTOM_THRESHOLD_WORDS)
    assert summary["required_common_carrier_compactness_theorem_flags"]
    assert not all(
        flag["value"] is True
        for flag in summary["required_common_carrier_compactness_theorem_flags"]
    )


def test_sprint110_fixture_guards_detect_placeholders_promotion_and_empty_data(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    write_sprint_module(
        tmp_path,
        110,
        "CommonCarrierCompactnessGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint110CommonCarrierCompactnessGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            clayYangMillsPromoted : Bool
            clayYangMillsPromoted = {promoted}

            {dangerous} FutureLemma : Set

            data FutureReceipt : Set where
            """
        ),
    )

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["hard_fail_reasons"]
    assert matching_items(summary, ("promotion",)) or matching_items(summary, ("clay",))
    assert matching_items(summary, ("incomplete", "surface"))
    assert matching_items(summary, ("empty", "data"))


def test_sprint109_110_real_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint109_110_modules()
    if not module_paths:
        pytest.skip("Sprint109/Sprint110 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint110_test_source_avoids_literal_placeholder_and_promotion_guards() -> None:
    source = Path(__file__).read_text()
    assert ("post" + "ulate FutureLemma") not in source
    assert ("clayYangMillsPromoted = " + "true") not in source


def test_sprint109_110_real_modules_record_required_evidence_surface() -> None:
    module_paths = sprint109_110_modules()
    if not module_paths:
        pytest.skip("Sprint109/Sprint110 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, COMMON_CARRIER_WORDS)
    assert matching_items(combined, WEAK_COMPACTNESS_WORDS)
    assert matching_items(combined, LOWER_SEMICONTINUITY_WORDS)
    assert matching_items(combined, RECOVERY_LIMSUP_WORDS)
    assert matching_items(combined, BOTTOM_THRESHOLD_WORDS)


def test_sprint110_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 110, "CommonCarrierCompactnessAuditFixture", sprint110_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 110 Common Carrier Compactness Audit" in report
    assert "Common Carrier Evidence" in report
    assert "Weak Compactness Evidence" in report
    assert "Closed-Form Lower Semicontinuity Evidence" in report
    assert "Recovery Core Density/Energy Limsup Evidence" in report
    assert "Bottom Sector/Threshold/No-Collapse Evidence" in report
    assert json_text(summary)
