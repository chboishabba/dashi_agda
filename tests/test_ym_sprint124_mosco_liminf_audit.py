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
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint124_mosco_liminf_audit.py"
SUMMARY_NAME = "ym_sprint124_mosco_liminf_audit_summary.json"
REPORT_NAME = "ym_sprint124_mosco_liminf_audit.md"
CLAY_NAME = "clay" + "Yang" + "Mills" + "Promoted"

pytestmark = pytest.mark.skipif(
    not SCRIPT.exists(),
    reason="Sprint124 Mosco liminf audit script is not integrated yet",
)

FORBIDDEN_WORD_PATTERNS = {
    "post" + "ulate": re.compile(r"\bpost" + "ulate\b"),
    "TO" + "DO": re.compile(r"\bTO" + "DO\b"),
    "stu" + "b": re.compile(r"\bstu" + "b\b", re.IGNORECASE),
    "PLACE" + "HOLDER": re.compile(r"\bPLACE" + "HOLDER\b", re.IGNORECASE),
}
FORBIDDEN_TOKENS = ("{" + "!", "!" + "}", "XXX")
EVIDENCE_EMPTY_SECTION_PATTERNS = (
    re.compile(r"##+\s+Manuscript\b[\s\S]{0,700}\bNo matching evidence was extracted\.", re.IGNORECASE),
    re.compile(r"##+\s+Manuscript\b[\s\S]{0,700}\bNo evidence\b", re.IGNORECASE),
    re.compile(r"##+\s+Route\b[\s\S]{0,700}\bNo matching evidence was extracted\.", re.IGNORECASE),
    re.compile(r"##+\s+Route\b[\s\S]{0,700}\bNo evidence\b", re.IGNORECASE),
    re.compile(r"##+\s+Evidence-Free\s+(?:Manuscript|Route)\b", re.IGNORECASE),
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
        candidates = sorted(out_dir.glob("*mosco*liminf*audit*.json"))
        assert candidates, result.stdout + result.stderr
        summary_path = candidates[0]

    return json.loads(summary_path.read_text(encoding="utf-8"))


def write_sprint_module(repo_root: Path, sprint: int, name: str, text: str) -> Path:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    path = module_dir / f"YMSprint{sprint}{name}.agda"
    path.write_text(text, encoding="utf-8")
    return path


def sprint124_fixture_module(flag_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint124MoscoLiminfAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        moscoLiminfLowerSemicontinuityProofFlag : Bool
        moscoLiminfLowerSemicontinuityProofFlag = {flag_value}

        moscoLiminfRecoveryCompatibilityProofFlag : Bool
        moscoLiminfRecoveryCompatibilityProofFlag = {flag_value}

        moscoLiminfWeakLimitEnergyBoundProofFlag : Bool
        moscoLiminfWeakLimitEnergyBoundProofFlag = {flag_value}

        moscoLiminfCommonCarrierTransferProofFlag : Bool
        moscoLiminfCommonCarrierTransferProofFlag = {flag_value}

        moscoLiminfManuscriptRouteProofFlag : Bool
        moscoLiminfManuscriptRouteProofFlag = {flag_value}

        moscoLiminfLowerSemicontinuityEvidenceText : String
        moscoLiminfLowerSemicontinuityEvidenceText =
          "Sprint124 Mosco liminf evidence records lower semicontinuity for weak limits, energy comparison, and nonnegative defect control."

        moscoLiminfRecoveryCompatibilityEvidenceText : String
        moscoLiminfRecoveryCompatibilityEvidenceText =
          "Sprint124 recovery compatibility evidence records Mosco recovery sequence alignment with the common carrier transfer calculus."

        moscoLiminfWeakLimitEnergyBoundEvidenceText : String
        moscoLiminfWeakLimitEnergyBoundEvidenceText =
          "Sprint124 weak limit energy bound evidence records liminf inequality rows with bounded energy and sector-stable convergence."

        moscoLiminfManuscriptEvidenceText : String
        moscoLiminfManuscriptEvidenceText =
          "Manuscript evidence records the Mosco liminf proposition, dependencies, blocked obligations, and citation-ready lower-bound route."

        moscoLiminfRouteEvidenceText : String
        moscoLiminfRouteEvidenceText =
          "Route evidence records fail-closed decision while dependencies remain false, no Clay promotion, and required next proof obligations."

        data Sprint124MoscoLiminfReceipt : Set where
          recorded :
            Sprint124MoscoLiminfReceipt
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
        if word.startswith("lim"):
            words.add("liminf")
        if word.startswith("semicont"):
            words.add("semicontinuity")
        if word.startswith("depend"):
            words.add("dependencies")
        if word.startswith("promot"):
            words.add("promotion")
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
        and re.search(r"mosco|liminf|lower|weak|energy|carrier|route|manuscript", json.dumps(item), re.IGNORECASE)
    ]
    if not flags:
        flags = [
            item
            for item in flatten_values(summary)
            if isinstance(item, dict)
            and set(item) >= {"name", "value"}
            and re.search(r"mosco|liminf|lower|weak|energy|carrier|route|manuscript", str(item["name"]), re.IGNORECASE)
        ]
    assert flags, "summary should expose Sprint124 Mosco liminf proof flags with boolean values"
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


def evidence_rows(summary: dict[str, Any]) -> list[dict[str, Any]]:
    rows = [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict)
        and re.search(r"evidence|line|row|path|text|source", json.dumps(item), re.IGNORECASE)
        and any(key in item for key in ("line", "text", "path", "source", "evidence", "rows"))
    ]
    concrete = [
        row
        for row in rows
        if (
            isinstance(row.get("line"), int)
            or isinstance(row.get("text"), str)
            or isinstance(row.get("path"), str)
            or isinstance(row.get("source"), str)
        )
    ]
    assert concrete, "summary should include concrete source-backed evidence rows"
    return concrete


def assert_json_and_markdown_outputs(out_dir: Path) -> None:
    assert (out_dir / SUMMARY_NAME).exists() or sorted(out_dir.glob("*mosco*liminf*audit*.json"))
    assert (out_dir / REPORT_NAME).exists() or sorted(out_dir.glob("*mosco*liminf*audit*.md"))


def assert_required_terms_present(text: str, summary: dict[str, Any]) -> None:
    combined = text + "\n" + json.dumps(summary, sort_keys=True)
    for phrase in (
        ("mosco",),
        ("liminf",),
        ("lower", "semicontinuity"),
        ("weak", "limit"),
        ("energy", "bound"),
        ("manuscript", "evidence"),
        ("route", "evidence"),
        ("fail", "closed"),
    ):
        assert matching_items(combined, phrase), f"missing Sprint124 term coverage: {' '.join(phrase)}"


def assert_no_forbidden_or_evidence_empty_output(text: str) -> None:
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
    for pattern in EVIDENCE_EMPTY_SECTION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_sprint124_mosco_liminf_cli_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 124, "MoscoLiminfAuditFixture", sprint124_fixture_module())

    summary = run_script(tmp_path, out_dir)
    text = output_text(out_dir, summary)

    assert_json_and_markdown_outputs(out_dir)
    assert "Sprint 124" in text or "Sprint124" in text
    assert "Mosco" in text
    assert "liminf" in text.lower()
    assert_required_terms_present(text, summary)


def test_sprint124_mosco_liminf_fails_closed_while_dependencies_are_false(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 124, "MoscoLiminfAuditFixture", sprint124_fixture_module("false"))

    summary = run_script(tmp_path, out_dir)
    flags = proof_flags(summary)

    assert summary["route_decision"] == "fail-closed"
    assert not all(flag["value"] is True for flag in flags)
    assert matching_items(summary, ("dependencies",)) or matching_items(summary, ("proof", "false"))
    assert matching_items(summary, ("fail", "closed"))


def test_sprint124_mosco_liminf_outputs_are_evidence_backed_and_non_promoting(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 124, "MoscoLiminfAuditFixture", sprint124_fixture_module())

    summary = run_script(tmp_path, out_dir)
    text = output_text(out_dir, summary)

    assert all(flag["value"] is False for flag in promotion_flags(summary))
    assert len(evidence_rows(summary)) >= 3
    assert_required_terms_present(text, summary)
    assert_no_forbidden_or_evidence_empty_output(text)


def test_sprint124_real_repo_summary_is_fail_closed_evidence_backed_and_non_promoting(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(REPO_ROOT, out_dir)
    text = output_text(out_dir, summary)

    assert summary["route_decision"] == "fail-closed"
    assert not all(flag["value"] is True for flag in proof_flags(summary))
    assert all(flag["value"] is False for flag in promotion_flags(summary))
    assert len(evidence_rows(summary)) >= 3
    assert_required_terms_present(text, summary)
    assert_no_forbidden_or_evidence_empty_output(text)
