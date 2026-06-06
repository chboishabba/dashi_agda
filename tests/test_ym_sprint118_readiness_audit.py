from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint118_readiness_audit.py"
SUMMARY_NAME = "ym_sprint118_readiness_audit_summary.json"
REPORT_NAME = "ym_sprint118_readiness_audit.md"
MODULE_GLOBS = ("YMSprint117*.agda", "YMSprint118*.agda")

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

EVIDENCE_KEYS = (
    "criterion_feed_aggregator_evidence",
    "carrier_construction_readiness_evidence",
    "mosco_compactness_readiness_evidence",
    "transfer_calculus_readiness_evidence",
    "transfer_blocker_matrix_evidence",
)
CRITERION_FEED_WORDS = ("criterion", "feed", "aggregator")
CARRIER_CONSTRUCTION_WORDS = ("carrier", "construction", "readiness")
MOSCO_COMPACTNESS_WORDS = ("mosco", "compactness", "readiness")
TRANSFER_CALCULUS_WORDS = ("transfer", "calculus", "readiness")
BLOCKER_MATRIX_WORDS = ("transfer", "blocker", "matrix")
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


def sprint117_context_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint117ReadinessAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        criterionFeedAggregatorContextFlag : Bool
        criterionFeedAggregatorContextFlag = true

        sprint117ReadinessContextText : String
        sprint117ReadinessContextText =
          "Sprint117 supplies criterion feed aggregator evidence, carrier construction readiness evidence, Mosco compactness readiness evidence, transfer calculus readiness evidence, and transfer blocker matrix evidence."

        data Sprint117ReadinessContextReceipt : Set where
          recorded :
            Sprint117ReadinessContextReceipt
        """
    )


def sprint118_fixture_module(false_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint118ReadinessAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        criterionFeedAggregatorReadinessProofFlag : Bool
        criterionFeedAggregatorReadinessProofFlag = {false_value}

        carrierConstructionReadinessProofFlag : Bool
        carrierConstructionReadinessProofFlag = {false_value}

        moscoCompactnessReadinessProofFlag : Bool
        moscoCompactnessReadinessProofFlag = {false_value}

        transferCalculusReadinessProofFlag : Bool
        transferCalculusReadinessProofFlag = {false_value}

        transferBlockerMatrixReadinessProofFlag : Bool
        transferBlockerMatrixReadinessProofFlag = {false_value}

        criterionFeedAggregatorEvidenceText : String
        criterionFeedAggregatorEvidenceText =
          "criterion feed aggregator evidence records norm, residual, and sector feeds from Sprint117"

        carrierConstructionReadinessEvidenceText : String
        carrierConstructionReadinessEvidenceText =
          "carrier construction readiness evidence records external common carrier construction, E_a/P_a, quotient, and sector requirements"

        moscoCompactnessReadinessEvidenceText : String
        moscoCompactnessReadinessEvidenceText =
          "Mosco compactness readiness evidence records weak compactness, no pollution, and no collapse requirements"

        transferCalculusReadinessEvidenceText : String
        transferCalculusReadinessEvidenceText =
          "transfer calculus readiness evidence records uniform form lower bound, log generator calculus, and spectral transport"

        transferBlockerMatrixEvidenceText : String
        transferBlockerMatrixEvidenceText =
          "transfer blocker matrix evidence records obligations and fail-closed rows for every not externally discharged readiness lane"

        data ReadinessReceipt : Set where
          recorded :
            ReadinessReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("aggregat"):
            words.add("aggregator")
        if word.startswith("criter"):
            words.add("criterion")
        if word.startswith("read"):
            words.add("readiness")
        if word.startswith("compact"):
            words.add("compactness")
        if word.startswith("calc"):
            words.add("calculus")
        if word.startswith("block"):
            words.add("blocker")
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


def assert_summary_records_readiness_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, CRITERION_FEED_WORDS)
    assert matching_items(summary, CARRIER_CONSTRUCTION_WORDS)
    assert matching_items(summary, MOSCO_COMPACTNESS_WORDS)
    assert matching_items(summary, TRANSFER_CALCULUS_WORDS)
    assert matching_items(summary, BLOCKER_MATRIX_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    for key in EVIDENCE_KEYS:
        assert summary[key], key
    assert summary["required_sprint118_readiness_proof_flags"]
    assert not all(flag["value"] is True for flag in summary["required_sprint118_readiness_proof_flags"])


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


def sprint117_118_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint118_fixture_summary_fails_closed_until_readiness_flags_true(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 117, "ReadinessAuditContext", sprint117_context_module())
    write_sprint_module(tmp_path, 118, "ReadinessAuditFixture", sprint118_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_readiness_audit(summary)
    assert summary["scanned_surfaces"]["sprint117"] == [
        "DASHI/Physics/Closure/YMSprint117ReadinessAuditContext.agda"
    ]
    assert summary["scanned_surfaces"]["sprint118"] == [
        "DASHI/Physics/Closure/YMSprint118ReadinessAuditFixture.agda"
    ]


def test_sprint118_fixture_guards_detect_placeholders_promotion_empty_data_and_metas(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    meta = "?"
    write_sprint_module(
        tmp_path,
        118,
        "ReadinessGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint118ReadinessGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            clayYangMillsPromoted : Bool
            clayYangMillsPromoted = {promoted}

            {dangerous} FutureReadinessLemma : Set

            unresolvedWitness : {meta}
            unresolvedWitness = {meta}

            data FutureReadinessReceipt : Set where
            """
        ),
    )

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["hard_fail_reasons"]
    assert matching_items(summary, ("promotion",)) or matching_items(summary, ("clay",))
    assert matching_items(summary, ("incomplete", "surface"))
    assert matching_items(summary, ("empty", "data"))
    assert "rhs-meta" in json_text(summary)
    assert "type-meta" in json_text(summary)


def test_sprint118_all_required_true_can_pass_when_no_route_or_hard_failures(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 117, "ReadinessAuditContext", sprint117_context_module())
    write_sprint_module(tmp_path, 118, "ReadinessAuditFixture", sprint118_fixture_module("true"))

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "sprint118 readiness proved"
    assert not summary["fail_reasons"]
    assert all(flag["value"] is True for flag in summary["required_sprint118_readiness_proof_flags"])


def test_sprint117_118_real_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint117_118_modules()
    if not module_paths:
        pytest.skip("Sprint117/Sprint118 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint118_script_and_test_source_avoid_literal_guard_triggers() -> None:
    for source_path in (SCRIPT, Path(__file__)):
        source = source_path.read_text()
        assert ("post" + "ulate FutureReadinessLemma") not in source
        assert ("TO" + "DO") not in source
        assert ("stu" + "b") not in source.lower()
        assert ("{" + "!") not in source
        assert ("!" + "}") not in source
        assert ("clayYangMillsPromoted = " + "true") not in source


def test_sprint117_real_modules_record_readiness_input_evidence() -> None:
    module_paths = sprint117_118_modules()
    if not module_paths:
        pytest.skip("Sprint117/Sprint118 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, CRITERION_FEED_WORDS)
    assert matching_items(combined, CARRIER_CONSTRUCTION_WORDS)
    assert matching_items(combined, MOSCO_COMPACTNESS_WORDS)
    assert matching_items(combined, TRANSFER_CALCULUS_WORDS)
    assert matching_items(combined, BLOCKER_MATRIX_WORDS)


def test_sprint118_real_summary_fails_closed_until_readiness_flags_are_true(
    tmp_path: Path,
) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["scanned_surfaces"]["sprint117"]
    if summary["scanned_surfaces"]["sprint118"]:
        assert summary["required_sprint118_readiness_proof_flags"]
        assert not all(flag["value"] is True for flag in summary["required_sprint118_readiness_proof_flags"])
    else:
        assert not summary["required_sprint118_readiness_proof_flags"]
    assert matching_items(summary["route_reasons"], ("sprint118",))
    for key in EVIDENCE_KEYS:
        assert summary[key], key


def test_sprint118_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 117, "ReadinessAuditContext", sprint117_context_module())
    write_sprint_module(tmp_path, 118, "ReadinessAuditFixture", sprint118_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 118 Readiness Audit" in report
    assert "Criterion Feed Aggregator Evidence" in report
    assert "Carrier Construction Readiness Evidence" in report
    assert "Mosco Compactness Readiness Evidence" in report
    assert "Transfer Calculus Readiness Evidence" in report
    assert "Transfer Blocker Matrix Evidence" in report
    assert json_text(summary)
