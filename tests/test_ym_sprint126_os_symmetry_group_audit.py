from __future__ import annotations

import json
import re
import subprocess
import sys
import textwrap
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint126_os_symmetry_group_audit.py"
SUMMARY_NAME = "ym_sprint126_os_symmetry_group_audit_summary.json"
REPORT_NAME = "ym_sprint126_os_symmetry_group_audit.md"
CLAY_NAME = "clay" + "Yang" + "Mills" + "Promoted"


def run_script(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    assert SCRIPT.exists(), "Sprint126 OS symmetry group audit script should be integrated"
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
        candidates = sorted(out_dir.glob("*sprint126*os*symmetry*group*audit*.json"))
        assert candidates, result.stdout + result.stderr
        summary_path = candidates[0]
    return json.loads(summary_path.read_text(encoding="utf-8"))


def write_sprint_module(repo_root: Path, sprint: int, name: str, text: str) -> Path:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    path = module_dir / f"YMSprint{sprint}{name}.agda"
    path.write_text(text, encoding="utf-8")
    return path


def sprint126_fixture_module(flag_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint126OSSymmetryGroupAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        os1OsterwalderSchraderReflectionProofFlag : Bool
        os1OsterwalderSchraderReflectionProofFlag = {flag_value}

        sy1SymmetryGroupActionProofFlag : Bool
        sy1SymmetryGroupActionProofFlag = {flag_value}

        gg1CompactGaugeGroupConstructionProofFlag : Bool
        gg1CompactGaugeGroupConstructionProofFlag = {flag_value}

        osSymmetryGroupRouteProofFlag : Bool
        osSymmetryGroupRouteProofFlag = {flag_value}

        os1EvidenceText : String
        os1EvidenceText =
          "OS1 evidence records Osterwalder-Schrader reflection positivity, Euclidean invariance, and reconstruction blockers."

        sy1EvidenceText : String
        sy1EvidenceText =
          "SY1 evidence records symmetry group action coherence, covariance, and transfer compatibility blockers."

        gg1EvidenceText : String
        gg1EvidenceText =
          "GG1 evidence records compact gauge group construction, group parameter coverage, and faithful action blockers."

        osSymmetryGroupRouteEvidenceText : String
        osSymmetryGroupRouteEvidenceText =
          "Route evidence records fail-closed decision while OS1, SY1, and GG1 dependencies remain false with no Clay promotion."
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
        if word.startswith("depend"):
            words.add("dependencies")
        if word.startswith("promot"):
            words.add("promotion")
        if word.startswith("osterwalder") or word.startswith("schrader"):
            words.add("os1")
        if word.startswith("symmetr"):
            words.add("sy1")
        if word.startswith("gauge") or word.startswith("group"):
            words.add("gg1")
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
        and re.search(r"os1|sy1|gg1|osterwalder|schrader|symmetry|group|gauge|route", json.dumps(item), re.IGNORECASE)
    ]
    if not flags:
        flags = [
            item
            for item in flatten_values(summary)
            if isinstance(item, dict)
            and set(item) >= {"name", "value"}
            and re.search(r"os1|sy1|gg1|osterwalder|schrader|symmetry|group|gauge|route", str(item["name"]), re.IGNORECASE)
        ]
    assert flags, "summary should expose Sprint126 OS/symmetry/group proof flags with boolean values"
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
        and any(key in item for key in ("line", "text", "path", "source", "sources", "evidence", "rows"))
    ]
    concrete = [
        row
        for row in rows
        if (
            isinstance(row.get("line"), int)
            or isinstance(row.get("text"), str)
            or isinstance(row.get("path"), str)
            or isinstance(row.get("source"), str)
            or isinstance(row.get("sources"), list)
        )
    ]
    assert concrete, "summary should include concrete source-backed evidence rows"
    return concrete


def assert_json_and_markdown_outputs(out_dir: Path) -> None:
    assert (out_dir / SUMMARY_NAME).exists() or sorted(out_dir.glob("*sprint126*os*symmetry*group*audit*.json"))
    assert (out_dir / REPORT_NAME).exists() or sorted(out_dir.glob("*sprint126*os*symmetry*group*audit*.md"))


def assert_required_blockers_present(value: Any) -> None:
    for phrase in (("os1",), ("sy1",), ("gg1",)):
        assert matching_items(value, phrase), f"missing required blocker coverage: {' '.join(phrase)}"


def assert_required_terms_present(text: str, summary: dict[str, Any]) -> None:
    combined = text + "\n" + json.dumps(summary, sort_keys=True)
    for phrase in (
        ("sprint126",),
        ("os1",),
        ("sy1",),
        ("gg1",),
        ("symmetry", "group"),
        ("fail", "closed"),
    ):
        assert matching_items(combined, phrase), f"missing Sprint126 term coverage: {' '.join(phrase)}"


def assert_no_clay_promotion(text: str, summary: dict[str, Any]) -> None:
    assert all(flag["value"] is False for flag in promotion_flags(summary))
    for promotion_true in (
        CLAY_NAME + " = " + "tr" + "ue",
        CLAY_NAME + '": ' + "tr" + "ue",
        CLAY_NAME + ": " + "tr" + "ue",
    ):
        assert promotion_true not in text


def assert_evidence_sources_non_empty(summary: dict[str, Any]) -> None:
    source_rows = []
    for row in evidence_rows(summary):
        source = row.get("source")
        sources = row.get("sources")
        path = row.get("path")
        if isinstance(source, str):
            source_rows.append(source.strip())
        if isinstance(path, str):
            source_rows.append(path.strip())
        if isinstance(sources, list):
            source_rows.extend(str(item).strip() for item in sources)
    assert source_rows, "generated evidence should expose non-empty sources"
    assert all(source for source in source_rows)


def test_sprint126_os_symmetry_group_cli_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 126, "OSSymmetryGroupAuditFixture", sprint126_fixture_module())

    summary = run_script(tmp_path, out_dir)
    text = output_text(out_dir, summary)

    assert_json_and_markdown_outputs(out_dir)
    assert "Sprint 126" in text or "Sprint126" in text
    assert "symmetry group" in text.lower() or "SymmetryGroup" in text
    assert_required_terms_present(text, summary)


def test_sprint126_os_symmetry_group_fails_closed_while_dependencies_are_false(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 126, "OSSymmetryGroupAuditFixture", sprint126_fixture_module("false"))

    summary = run_script(tmp_path, out_dir)
    flags = proof_flags(summary)

    assert summary["route_decision"] == "fail-closed"
    assert not all(flag["value"] is True for flag in flags)
    assert matching_items(summary, ("dependencies",)) or matching_items(summary, ("proof", "false"))
    assert matching_items(summary, ("fail", "closed"))


def test_sprint126_os_symmetry_group_outputs_include_blockers_sources_and_no_clay_promotion(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 126, "OSSymmetryGroupAuditFixture", sprint126_fixture_module())

    summary = run_script(tmp_path, out_dir)
    text = output_text(out_dir, summary)

    assert_required_blockers_present(summary)
    assert len(evidence_rows(summary)) >= 3
    assert_evidence_sources_non_empty(summary)
    assert_required_terms_present(text, summary)
    assert_no_clay_promotion(text, summary)
