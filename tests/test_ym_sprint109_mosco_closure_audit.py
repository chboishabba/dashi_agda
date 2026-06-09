from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint109_mosco_closure_audit.py"
SUMMARY_NAME = "ym_sprint109_mosco_closure_audit_summary.json"
REPORT_NAME = "ym_sprint109_mosco_closure_audit.md"
MODULE_GLOB = "YMSprint109*.agda"

TRANSFER_GAP_TARGET = "gap(T(a)) >= c * m_eff(a) * a"
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

LOWER_SEMICONTINUITY_WORDS = ("lower", "semicontinuity")
RECOVERY_SEQUENCE_WORDS = ("recovery", "sequence")
NO_BOTTOM_POLLUTION_WORDS = ("bottom", "spectrum", "pollution")
SPECTRAL_LIMINF_WORDS = ("spectral", "liminf")
TRANSFER_CRITICAL_WORDS = ("transfer", "lower", "bound", "assembly")
FAIL_CLOSED_WORDS = ("fail", "closed")


def run_script(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    if not SCRIPT.exists():
        pytest.skip("Sprint109 Mosco closure audit script is not integrated yet")

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


def write_sprint109_module(repo_root: Path, name: str, text: str) -> Path:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    path = module_dir / f"YMSprint109{name}.agda"
    path.write_text(text)
    return path


def sprint109_fixture_module() -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint109MoscoClosureAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        lowerSemicontinuityClosureTheoremProved : Bool
        lowerSemicontinuityClosureTheoremProved = false

        recoverySequenceClosureTheoremProved : Bool
        recoverySequenceClosureTheoremProved = false

        noBottomSpectrumPollutionClosureTheoremProved : Bool
        noBottomSpectrumPollutionClosureTheoremProved = false

        spectralLiminfAssemblyTheoremProved : Bool
        spectralLiminfAssemblyTheoremProved = false

        transferLowerBoundCriticalAssemblyTheoremProved : Bool
        transferLowerBoundCriticalAssemblyTheoremProved = false

        targetFormulaText : String
        targetFormulaText =
          "{TRANSFER_GAP_TARGET}"

        lowerSemicontinuityEvidenceText : String
        lowerSemicontinuityEvidenceText =
          "lower semicontinuity evidence records Mosco liminf control for quadratic forms"

        recoverySequenceEvidenceText : String
        recoverySequenceEvidenceText =
          "recovery sequence evidence supplies approximants with matching norm and energy limit"

        noBottomSpectrumPollutionEvidenceText : String
        noBottomSpectrumPollutionEvidenceText =
          "no bottom-spectrum pollution evidence excludes spurious eigenvalue branches"

        spectralLiminfAssemblyEvidenceText : String
        spectralLiminfAssemblyEvidenceText =
          "spectral liminf assembly evidence links finite bottom spectra to continuum lower bounds"

        transferLowerBoundCriticalAssemblyEvidenceText : String
        transferLowerBoundCriticalAssemblyEvidenceText =
          "transfer lower-bound critical assembly evidence keeps the route fail-closed"

        data MoscoClosureReceipt : Set where
          recorded :
            MoscoClosureReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("semicont"):
            words.add("semicontinuity")
        if word.startswith("recover"):
            words.add("recovery")
        if word.startswith("pollut"):
            words.add("pollution")
        if word.startswith("spectr"):
            words.add("spectral")
        if word.startswith("liminf"):
            words.add("liminf")
        if word.startswith("assembl"):
            words.add("assembly")
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


def assert_summary_records_mosco_closure_audit(summary: dict[str, Any]) -> None:
    serialized = json_text(summary)

    assert summary["route_decision"] == "fail-closed"
    assert TRANSFER_GAP_TARGET in serialized
    assert matching_items(summary, LOWER_SEMICONTINUITY_WORDS)
    assert matching_items(summary, RECOVERY_SEQUENCE_WORDS)
    assert matching_items(summary, NO_BOTTOM_POLLUTION_WORDS)
    assert matching_items(summary, SPECTRAL_LIMINF_WORDS)
    assert matching_items(summary, TRANSFER_CRITICAL_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    assert summary["required_mosco_closure_theorem_flags"]
    assert not all(flag["value"] is True for flag in summary["required_mosco_closure_theorem_flags"])


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


def sprint109_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    return sorted((repo_root / "DASHI" / "Physics" / "Closure").glob(MODULE_GLOB))


def test_sprint109_fixture_summary_records_mosco_closure_audit(tmp_path: Path) -> None:
    write_sprint109_module(tmp_path, "MoscoClosureAuditFixture", sprint109_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_mosco_closure_audit(summary)
    assert summary["scanned_surfaces"]["sprint109"] == [
        "DASHI/Physics/Closure/YMSprint109MoscoClosureAuditFixture.agda"
    ]


def test_sprint109_real_summary_records_fail_closed_mosco_closure_audit(tmp_path: Path) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, LOWER_SEMICONTINUITY_WORDS)
    assert matching_items(summary, RECOVERY_SEQUENCE_WORDS)
    assert matching_items(summary, NO_BOTTOM_POLLUTION_WORDS)
    assert matching_items(summary, SPECTRAL_LIMINF_WORDS)
    assert matching_items(summary, TRANSFER_CRITICAL_WORDS)
    assert summary["required_mosco_closure_theorem_flags"]
    assert not all(flag["value"] is True for flag in summary["required_mosco_closure_theorem_flags"])


def test_sprint109_fixture_guards_detect_placeholders_promotion_and_empty_data(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    write_sprint109_module(
        tmp_path,
        "MoscoClosureGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint109MoscoClosureGuardFixture where

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


def test_sprint109_real_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint109_modules()
    if not module_paths:
        pytest.skip("Sprint109 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint109_real_modules_record_manuscript_and_evidence_surface() -> None:
    module_paths = sprint109_modules()
    if not module_paths:
        pytest.skip("Sprint109 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert TRANSFER_GAP_TARGET in combined
    assert matching_items(combined, LOWER_SEMICONTINUITY_WORDS)
    assert matching_items(combined, RECOVERY_SEQUENCE_WORDS)
    assert matching_items(combined, NO_BOTTOM_POLLUTION_WORDS)
    assert matching_items(combined, SPECTRAL_LIMINF_WORDS)
    assert matching_items(combined, TRANSFER_CRITICAL_WORDS)


def test_sprint109_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint109_module(tmp_path, "MoscoClosureAuditFixture", sprint109_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 109 Mosco Closure Audit" in report
    assert "Lower Semicontinuity Evidence" in report
    assert "Recovery Sequence Evidence" in report
    assert "No-Bottom-Spectrum Pollution Evidence" in report
    assert "Spectral Liminf Assembly Evidence" in report
    assert "Transfer Lower-Bound Critical Assembly Evidence" in report
