from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint119_unlock_audit.py"
SUMMARY_NAME = "ym_sprint119_unlock_audit_summary.json"
REPORT_NAME = "ym_sprint119_unlock_audit.md"
MODULE_GLOBS = ("YMSprint118*.agda", "YMSprint119*.agda")
CLAY_NAME = "clay" + "Yang" + "Mills" + "Promoted"

FORBIDDEN_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
    "{" + "!",
    "!" + "}",
)
FORBIDDEN_PROMOTION = CLAY_NAME + " = " + "tr" + "ue"
FORBIDDEN_WORD_PATTERNS = {
    "post" + "ulate": re.compile(r"\bpost" + "ulate\b"),
    "TO" + "DO": re.compile(r"\bTO" + "DO\b"),
    "stu" + "b": re.compile(r"\bstu" + "b\b", re.IGNORECASE),
}

EVIDENCE_KEYS = (
    "common_carrier_feedthrough_unlock_evidence",
    "weak_compactness_obligation_reducer_evidence",
    "mosco_all_obligations_reducer_evidence",
    "transfer_calculus_all_obligations_reducer_evidence",
    "transfer_readiness_unlock_reducer_evidence",
)
COMMON_FEED_WORDS = ("common", "carrier", "feedthrough", "unlock")
WEAK_COMPACTNESS_WORDS = ("weak", "compactness", "obligation", "reducer")
MOSCO_ALL_WORDS = ("mosco", "all", "obligations", "reducer")
TRANSFER_CALCULUS_WORDS = ("transfer", "calculus", "all", "obligations", "reducer")
TRANSFER_UNLOCK_WORDS = ("transfer", "readiness", "unlock", "reducer")
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


def sprint118_context_module() -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint118UnlockAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        sprint118ReadinessContextFlag : Bool
        sprint118ReadinessContextFlag = true

        sprint118UnlockContextText : String
        sprint118UnlockContextText =
          "Sprint118 supplies common carrier feedthrough unlock inputs, weak compactness obligation reducer inputs, Mosco all obligations reducer inputs, transfer calculus all obligations reducer inputs, and transfer readiness unlock reducer inputs."

        data Sprint118UnlockContextReceipt : Set where
          recorded :
            Sprint118UnlockContextReceipt
        """
    )


def sprint119_fixture_module(false_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint119UnlockAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        commonCarrierFeedthroughUnlockProofFlag : Bool
        commonCarrierFeedthroughUnlockProofFlag = {false_value}

        weakCompactnessObligationReducerProofFlag : Bool
        weakCompactnessObligationReducerProofFlag = {false_value}

        moscoAllObligationsReducerProofFlag : Bool
        moscoAllObligationsReducerProofFlag = {false_value}

        transferCalculusAllObligationsReducerProofFlag : Bool
        transferCalculusAllObligationsReducerProofFlag = {false_value}

        transferReadinessUnlockReducerProofFlag : Bool
        transferReadinessUnlockReducerProofFlag = {false_value}

        commonCarrierFeedthroughUnlockEvidenceText : String
        commonCarrierFeedthroughUnlockEvidenceText =
          "common carrier feedthrough unlock evidence closes the criterion feed package and external carrier construction feed-through lane"

        weakCompactnessObligationReducerEvidenceText : String
        weakCompactnessObligationReducerEvidenceText =
          "weak compactness obligation reducer evidence records bounded energy subsequence extraction on the same common carrier"

        moscoAllObligationsReducerEvidenceText : String
        moscoAllObligationsReducerEvidenceText =
          "Mosco all obligations reducer evidence records liminf, recovery, no pollution, no collapse, weak compactness, and closed form LSC"

        transferCalculusAllObligationsReducerEvidenceText : String
        transferCalculusAllObligationsReducerEvidenceText =
          "transfer calculus all obligations reducer evidence records uniform form, log generator, spectral transport, and transfer assembly"

        transferReadinessUnlockReducerEvidenceText : String
        transferReadinessUnlockReducerEvidenceText =
          "transfer readiness unlock reducer evidence records lower-bound proof readiness and remains fail-closed until all reducers are discharged"

        data UnlockReceipt : Set where
          recorded :
            UnlockReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("compact"):
            words.add("compactness")
        if word.startswith("oblig"):
            words.add("obligations")
            words.add("obligation")
        if word.startswith("read"):
            words.add("readiness")
        if word.startswith("feed"):
            words.add("feedthrough")
        if word.startswith("calc"):
            words.add("calculus")
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


def assert_summary_records_unlock_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, COMMON_FEED_WORDS)
    assert matching_items(summary, WEAK_COMPACTNESS_WORDS)
    assert matching_items(summary, MOSCO_ALL_WORDS)
    assert matching_items(summary, TRANSFER_CALCULUS_WORDS)
    assert matching_items(summary, TRANSFER_UNLOCK_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    for key in EVIDENCE_KEYS:
        assert summary[key], key
    assert summary["required_sprint119_unlock_proof_flags"]
    assert not all(flag["value"] is True for flag in summary["required_sprint119_unlock_proof_flags"])


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


def sprint118_119_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint119_fixture_summary_fails_closed_until_unlock_flags_true(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 118, "UnlockAuditContext", sprint118_context_module())
    write_sprint_module(tmp_path, 119, "UnlockAuditFixture", sprint119_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_unlock_audit(summary)
    assert summary["scanned_surfaces"]["sprint118"] == [
        "DASHI/Physics/Closure/YMSprint118UnlockAuditContext.agda"
    ]
    assert summary["scanned_surfaces"]["sprint119"] == [
        "DASHI/Physics/Closure/YMSprint119UnlockAuditFixture.agda"
    ]


def test_sprint119_fixture_guards_detect_markers_promotion_empty_data_and_metas(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    meta = "?"
    write_sprint_module(
        tmp_path,
        119,
        "UnlockGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint119UnlockGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            {CLAY_NAME} : Bool
            {CLAY_NAME} = {promoted}

            {dangerous} FutureUnlockLemma : Set

            unresolvedWitness : {meta}
            unresolvedWitness = {meta}

            data FutureUnlockReceipt : Set where
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


def test_sprint119_all_required_true_can_pass_when_no_route_or_hard_failures(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 118, "UnlockAuditContext", sprint118_context_module())
    write_sprint_module(tmp_path, 119, "UnlockAuditFixture", sprint119_fixture_module("true"))

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "sprint119 unlock proved"
    assert not summary["fail_reasons"]
    assert all(flag["value"] is True for flag in summary["required_sprint119_unlock_proof_flags"])


def test_sprint118_119_real_modules_have_no_markers_empty_data_or_promotion() -> None:
    module_paths = sprint118_119_modules()
    if not module_paths:
        pytest.skip("Sprint118/Sprint119 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint119_script_and_test_source_avoid_literal_guard_triggers() -> None:
    for source_path in (SCRIPT, Path(__file__)):
        source = source_path.read_text()
        assert ("post" + "ulate FutureUnlockLemma") not in source
        assert ("TO" + "DO") not in source
        assert ("stu" + "b") not in source.lower()
        assert ("{" + "!") not in source
        assert ("!" + "}") not in source
        assert (CLAY_NAME + " = " + "tr" + "ue") not in source


def test_sprint118_real_modules_record_unlock_input_evidence() -> None:
    module_paths = sprint118_119_modules()
    if not module_paths:
        pytest.skip("Sprint118/Sprint119 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, ("common", "carrier"))
    assert matching_items(combined, ("weak", "compactness"))
    assert matching_items(combined, ("mosco", "obligation"))
    assert matching_items(combined, ("transfer", "calculus"))
    assert matching_items(combined, ("transfer", "readiness"))


def test_sprint119_real_summary_shape_is_fail_closed(tmp_path: Path) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["scanned_surfaces"]["sprint118"]
    assert "sprint119" in summary["scanned_surfaces"]
    assert "required_sprint119_unlock_proof_flags" in summary
    assert matching_items(summary["route_reasons"], ("sprint119",))
    for key in EVIDENCE_KEYS:
        assert key in summary
        assert summary[key], key


def test_sprint119_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 118, "UnlockAuditContext", sprint118_context_module())
    write_sprint_module(tmp_path, 119, "UnlockAuditFixture", sprint119_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 119 Unlock Audit" in report
    assert "Common Carrier Feedthrough Unlock Evidence" in report
    assert "Weak Compactness Obligation Reducer Evidence" in report
    assert "Mosco All Obligations Reducer Evidence" in report
    assert "Transfer Calculus All Obligations Reducer Evidence" in report
    assert "Transfer Readiness Unlock Reducer Evidence" in report
    assert json_text(summary)
