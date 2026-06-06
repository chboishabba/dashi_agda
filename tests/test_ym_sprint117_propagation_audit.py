from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint117_propagation_audit.py"
SUMMARY_NAME = "ym_sprint117_propagation_audit_summary.json"
REPORT_NAME = "ym_sprint117_propagation_audit.md"
MODULE_GLOBS = ("YMSprint116*.agda", "YMSprint117*.agda")

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
    "norm_criterion_propagator_evidence",
    "residual_criterion_propagator_evidence",
    "sector_criterion_propagator_evidence",
    "common_carrier_feedthrough_propagator_evidence",
    "transfer_readiness_obligation_evidence",
)
NORM_CRITERION_WORDS = ("norm", "criterion", "propagator")
RESIDUAL_CRITERION_WORDS = ("residual", "criterion", "propagator")
SECTOR_CRITERION_WORDS = ("sector", "criterion", "propagator")
COMMON_CARRIER_WORDS = ("common", "carrier", "feedthrough")
TRANSFER_READINESS_WORDS = ("transfer", "readiness", "obligation")
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


def sprint116_context_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint116PropagationAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        sprint116ClosureReducerRecorded : Bool
        sprint116ClosureReducerRecorded = true

        sprint116PropagationContextText : String
        sprint116PropagationContextText =
          "Sprint116 supplies norm criterion, residual criterion, sector criterion, common carrier feedthrough, and transfer readiness obligation context for Sprint117 propagation."

        data Sprint116PropagationContextReceipt : Set where
          recorded :
            Sprint116PropagationContextReceipt
        """
    )


def sprint117_fixture_module(false_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint117PropagationAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        normCriterionPropagatorProofFlag : Bool
        normCriterionPropagatorProofFlag = {false_value}

        residualCriterionPropagatorProofFlag : Bool
        residualCriterionPropagatorProofFlag = {false_value}

        sectorCriterionPropagatorProofFlag : Bool
        sectorCriterionPropagatorProofFlag = {false_value}

        commonCarrierFeedthroughPropagatorProofFlag : Bool
        commonCarrierFeedthroughPropagatorProofFlag = {false_value}

        transferReadinessObligationProofFlag : Bool
        transferReadinessObligationProofFlag = {false_value}

        normCriterionPropagatorEvidenceText : String
        normCriterionPropagatorEvidenceText =
          "norm criterion propagator evidence records gauge window compatibility, quotient constants, and Sprint116 norm reducer feed"

        residualCriterionPropagatorEvidenceText : String
        residualCriterionPropagatorEvidenceText =
          "residual criterion propagator evidence records convergence, vanishing rates, and Sprint116 residual reducer feed"

        sectorCriterionPropagatorEvidenceText : String
        sectorCriterionPropagatorEvidenceText =
          "sector criterion propagator evidence records projection stability, physical sector descent, and Sprint116 sector reducer feed"

        commonCarrierFeedthroughPropagatorEvidenceText : String
        commonCarrierFeedthroughPropagatorEvidenceText =
          "common carrier feedthrough propagator evidence records common carrier transfer feedthrough into the Sprint117 propagation surface"

        transferReadinessObligationEvidenceText : String
        transferReadinessObligationEvidenceText =
          "transfer readiness obligation evidence records lower bound readiness and the remaining transfer obligation without Clay promotion"

        data PropagationReceipt : Set where
          recorded :
            PropagationReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("propagat"):
            words.add("propagator")
        if word.startswith("resid"):
            words.add("residual")
        if word.startswith("feed"):
            words.add("feedthrough")
        if word.startswith("read"):
            words.add("readiness")
        if word.startswith("oblig"):
            words.add("obligation")
        if word.startswith("criter"):
            words.add("criterion")
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


def assert_summary_records_propagation_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, NORM_CRITERION_WORDS)
    assert matching_items(summary, RESIDUAL_CRITERION_WORDS)
    assert matching_items(summary, SECTOR_CRITERION_WORDS)
    assert matching_items(summary, COMMON_CARRIER_WORDS)
    assert matching_items(summary, TRANSFER_READINESS_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    for key in EVIDENCE_KEYS:
        assert summary[key], key
    assert summary["required_sprint117_propagation_proof_flags"]
    assert not all(
        flag["value"] is True
        for flag in summary["required_sprint117_propagation_proof_flags"]
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


def sprint116_117_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint117_fixture_summary_records_propagation_audit(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 116, "PropagationAuditContext", sprint116_context_module())
    write_sprint_module(tmp_path, 117, "PropagationAuditFixture", sprint117_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_propagation_audit(summary)
    assert summary["scanned_surfaces"]["sprint116"] == [
        "DASHI/Physics/Closure/YMSprint116PropagationAuditContext.agda"
    ]
    assert summary["scanned_surfaces"]["sprint117"] == [
        "DASHI/Physics/Closure/YMSprint117PropagationAuditFixture.agda"
    ]


def test_sprint117_fixture_guards_detect_placeholders_promotion_empty_data_and_metas(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    meta = "?"
    write_sprint_module(
        tmp_path,
        117,
        "PropagationGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint117PropagationGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            clayYangMillsPromoted : Bool
            clayYangMillsPromoted = {promoted}

            {dangerous} FuturePropagationLemma : Set

            unresolvedWitness : {meta}
            unresolvedWitness = {meta}

            data FuturePropagationReceipt : Set where
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


def test_sprint117_all_required_true_can_pass_when_no_route_or_hard_failures(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 116, "PropagationAuditContext", sprint116_context_module())
    write_sprint_module(tmp_path, 117, "PropagationAuditFixture", sprint117_fixture_module("true"))

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "propagation criteria proved"
    assert not summary["fail_reasons"]
    assert all(flag["value"] is True for flag in summary["required_sprint117_propagation_proof_flags"])


def test_sprint116_117_real_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint116_117_modules()
    if not module_paths:
        pytest.skip("Sprint116/Sprint117 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint117_script_and_test_source_avoid_literal_placeholder_and_promotion_guards() -> None:
    for source_path in (SCRIPT, Path(__file__)):
        source = source_path.read_text()
        assert ("post" + "ulate FuturePropagationLemma") not in source
        assert ("clayYangMillsPromoted = " + "true") not in source


def test_sprint116_real_modules_record_propagation_input_evidence() -> None:
    module_paths = sprint116_117_modules()
    if not module_paths:
        pytest.skip("Sprint116/Sprint117 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, NORM_CRITERION_WORDS)
    assert matching_items(combined, RESIDUAL_CRITERION_WORDS)
    assert matching_items(combined, SECTOR_CRITERION_WORDS)
    assert matching_items(combined, COMMON_CARRIER_WORDS)
    assert matching_items(combined, TRANSFER_READINESS_WORDS)


def test_sprint117_real_summary_fails_closed_until_propagation_flags_are_true(
    tmp_path: Path,
) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["scanned_surfaces"]["sprint116"]
    if summary["scanned_surfaces"]["sprint117"]:
        assert summary["required_sprint117_propagation_proof_flags"]
        assert not all(flag["value"] is True for flag in summary["required_sprint117_propagation_proof_flags"])
    else:
        assert not summary["required_sprint117_propagation_proof_flags"]
    assert matching_items(summary["route_reasons"], ("sprint117", "propagation", "proof"))
    for key in EVIDENCE_KEYS:
        assert summary[key], key


def test_sprint117_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 116, "PropagationAuditContext", sprint116_context_module())
    write_sprint_module(tmp_path, 117, "PropagationAuditFixture", sprint117_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 117 Propagation Audit" in report
    assert "Norm Criterion Propagator Evidence" in report
    assert "Residual Criterion Propagator Evidence" in report
    assert "Sector Criterion Propagator Evidence" in report
    assert "Common Carrier Feedthrough Propagator Evidence" in report
    assert "Transfer Readiness Obligation Evidence" in report
    assert json_text(summary)
