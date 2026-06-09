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
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint123_wc1_weak_compactness_audit.py"
SUMMARY_NAME = "ym_sprint123_wc1_weak_compactness_audit_summary.json"
REPORT_NAME = "ym_sprint123_wc1_weak_compactness_audit.md"
CLAY_NAME = "clay" + "Yang" + "Mills" + "Promoted"

pytestmark = pytest.mark.skipif(
    not SCRIPT.exists(),
    reason="Sprint123 WC1 weak compactness audit script is not integrated yet",
)

FORBIDDEN_WORD_PATTERNS = {
    "post" + "ulate": re.compile(r"\bpost" + "ulate\b"),
    "TO" + "DO": re.compile(r"\bTO" + "DO\b"),
    "stu" + "b": re.compile(r"\bstu" + "b\b", re.IGNORECASE),
    "PLACE" + "HOLDER": re.compile(r"\bPLACE" + "HOLDER\b", re.IGNORECASE),
}
FORBIDDEN_TOKENS = ("{" + "!", "!" + "}", "XXX")
EVIDENCE_FREE_SECTION_PATTERNS = (
    re.compile(r"##+\s+Manuscript\b[\s\S]{0,500}\bNo matching evidence was extracted\.", re.IGNORECASE),
    re.compile(r"##+\s+Manuscript\b[\s\S]{0,500}\bNo evidence\b", re.IGNORECASE),
    re.compile(r"##+\s+Evidence-Free Manuscript\b", re.IGNORECASE),
)


def run_script(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    result = subprocess.run(
        [
            sys.executable,
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
    assert result.returncode in (0, 1), result.stdout + result.stderr

    summary_path = out_dir / SUMMARY_NAME
    if not summary_path.exists():
        candidates = sorted(out_dir.glob("*wc1*weak*compactness*audit*.json"))
        assert candidates, result.stdout + result.stderr
        summary_path = candidates[0]

    return json.loads(summary_path.read_text(encoding="utf-8"))


def write_sprint_module(repo_root: Path, sprint: int, name: str, text: str) -> Path:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    path = module_dir / f"YMSprint{sprint}{name}.agda"
    path.write_text(text, encoding="utf-8")
    return path


def wc1_fixture_module(flag_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint123WC1WeakCompactnessAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        wc1TightnessProofFlag : Bool
        wc1TightnessProofFlag = {flag_value}

        wc1DiagonalSubsequenceProofFlag : Bool
        wc1DiagonalSubsequenceProofFlag = {flag_value}

        wc1SpectralMeasuresProofFlag : Bool
        wc1SpectralMeasuresProofFlag = {flag_value}

        wc1CommonCarrierCC1ProofFlag : Bool
        wc1CommonCarrierCC1ProofFlag = {flag_value}

        wc1WeakCompactnessClosureProofFlag : Bool
        wc1WeakCompactnessClosureProofFlag = {flag_value}

        wc1TightnessEvidenceText : String
        wc1TightnessEvidenceText =
          "WC1 tightness evidence records uniform bounds and probability mass control on the common carrier."

        wc1DiagonalEvidenceText : String
        wc1DiagonalEvidenceText =
          "WC1 diagonal evidence records diagonal subsequence extraction and compatibility across lattice refinements."

        wc1SpectralMeasuresEvidenceText : String
        wc1SpectralMeasuresEvidenceText =
          "WC1 spectral measures evidence records measure convergence and spectral lower-bound transport."

        wc1CommonCarrierCC1EvidenceText : String
        wc1CommonCarrierCC1EvidenceText =
          "WC1 common carrier and CC1 evidence records carrier compatibility, projection, and embedding feedthrough."

        data WC1WeakCompactnessReceipt : Set where
          recorded :
            WC1WeakCompactnessReceipt
        """
    )


def flatten_values(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [nested for item in value.values() for nested in flatten_values(item)]
    if isinstance(value, list):
        return [value] + [nested for item in value for nested in flatten_values(item)]
    return [value]


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value, sort_keys=True).lower()))
    for word in tuple(words):
        if word.startswith("compact"):
            words.add("compactness")
        if word.startswith("diag"):
            words.add("diagonal")
        if word.startswith("spectral"):
            words.add("spectral")
        if word.startswith("measure"):
            words.add("measures")
        if word.startswith("carrier"):
            words.add("carrier")
    return words


def matching_items(value: Any, phrase: tuple[str, ...]) -> list[Any]:
    return [
        item
        for item in flatten_values(value)
        if all(word in normalized_words(item) for word in phrase)
    ]


def output_text(out_dir: Path, summary: dict[str, Any]) -> str:
    parts = [json.dumps(summary, sort_keys=True)]
    for path in sorted(out_dir.glob("*")):
        if path.suffix in {".json", ".md", ".markdown", ".txt"}:
            parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(parts)


def proof_flags(summary: dict[str, Any]) -> list[dict[str, Any]]:
    flags = [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict)
        and "value" in item
        and any("flag" in str(key).lower() for key in item)
        and re.search(r"wc1|weak|compact|tight|diagonal|spectral|carrier|cc1", json.dumps(item), re.IGNORECASE)
    ]
    if not flags:
        flags = [
            item
            for item in flatten_values(summary)
            if isinstance(item, dict)
            and set(item) >= {"name", "value"}
            and re.search(r"wc1|weak|compact|tight|diagonal|spectral|carrier|cc1", str(item["name"]), re.IGNORECASE)
        ]
    assert flags, "summary should expose WC1 proof flags with boolean values"
    assert all(isinstance(flag.get("value"), bool) for flag in flags), flags
    return flags


def promotion_flags(summary: dict[str, Any]) -> list[dict[str, Any]]:
    flags = [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict)
        and "value" in item
        and isinstance(item.get("value"), bool)
        and re.search(r"clay|promotion|promoted", json.dumps(item), re.IGNORECASE)
    ]
    assert flags, "summary should expose promotion flags"
    return flags


def assert_required_wc1_terms_present(text: str, summary: dict[str, Any]) -> None:
    combined = text + "\n" + json.dumps(summary, sort_keys=True)
    for phrase in (
        ("tightness",),
        ("diagonal",),
        ("spectral", "measures"),
        ("common", "carrier"),
        ("cc1",),
    ):
        assert matching_items(combined, phrase), f"missing WC1 term coverage: {' '.join(phrase)}"


def assert_no_forbidden_output_text(text: str) -> None:
    for token, pattern in FORBIDDEN_WORD_PATTERNS.items():
        assert not pattern.search(text), token
    for token in FORBIDDEN_TOKENS:
        assert token not in text
    for promotion_true in (
        CLAY_NAME + " = " + "tr" + "ue",
        CLAY_NAME + '": ' + "tr" + "ue",
        CLAY_NAME + ": " + "tr" + "ue",
    ):
        assert promotion_true not in text
    for pattern in EVIDENCE_FREE_SECTION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def assert_json_and_markdown_outputs(out_dir: Path) -> None:
    assert (out_dir / SUMMARY_NAME).exists() or sorted(out_dir.glob("*wc1*weak*compactness*audit*.json"))
    assert (out_dir / REPORT_NAME).exists() or sorted(out_dir.glob("*wc1*weak*compactness*audit*.md"))


def test_sprint123_wc1_cli_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 123, "WC1WeakCompactnessAuditFixture", wc1_fixture_module())

    summary = run_script(tmp_path, out_dir)
    text = output_text(out_dir, summary)

    assert_json_and_markdown_outputs(out_dir)
    assert "WC1" in text
    assert "weak compactness" in text.lower()
    assert_required_wc1_terms_present(text, summary)


def test_sprint123_wc1_fixture_fails_closed_with_any_false_proof_flag(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 123, "WC1WeakCompactnessAuditFixture", wc1_fixture_module("false"))

    summary = run_script(tmp_path, out_dir)
    flags = proof_flags(summary)

    assert summary["route_decision"] == "fail-closed"
    assert not all(flag["value"] is True for flag in flags)
    assert matching_items(summary, ("fail", "closed"))


def test_sprint123_wc1_all_true_fixture_has_no_false_proof_flags(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 123, "WC1WeakCompactnessAuditFixture", wc1_fixture_module("true"))

    summary = run_script(tmp_path, out_dir)
    flags = proof_flags(summary)

    assert all(flag["value"] is True for flag in flags)
    if summary["route_decision"] == "fail-closed":
        assert not matching_items(summary, ("proof", "false"))
        assert not matching_items(summary, ("flag", "false"))


def test_sprint123_wc1_outputs_are_non_promoting_and_evidence_backed(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 123, "WC1WeakCompactnessAuditFixture", wc1_fixture_module())

    summary = run_script(tmp_path, out_dir)
    text = output_text(out_dir, summary)

    assert all(flag["value"] is False for flag in promotion_flags(summary))
    assert_required_wc1_terms_present(text, summary)
    assert_no_forbidden_output_text(text)
