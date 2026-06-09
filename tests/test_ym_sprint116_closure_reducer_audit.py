from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint116_closure_reducer_audit.py"
SUMMARY_NAME = "ym_sprint116_closure_reducer_audit_summary.json"
REPORT_NAME = "ym_sprint116_closure_reducer_audit.md"
MODULE_GLOBS = ("YMSprint115*.agda", "YMSprint116*.agda")

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
    "residual_convergence_reducer_evidence",
    "norm_gauge_window_reducer_evidence",
    "sector_stability_reducer_evidence",
    "approximate_inverse_reducer_evidence",
    "common_carrier_transfer_reducer_evidence",
)
RESIDUAL_CONVERGENCE_WORDS = ("residual", "convergence", "reducer")
NORM_GAUGE_WINDOW_WORDS = ("norm", "gauge", "window")
SECTOR_STABILITY_WORDS = ("sector", "stability", "reducer")
APPROXIMATE_INVERSE_WORDS = ("approximate", "inverse", "reducer")
COMMON_CARRIER_TRANSFER_WORDS = ("common", "carrier", "transfer")
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


def sprint115_context_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint115ClosureReducerAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        sprint115AnalyticSupplyRecorded : Bool
        sprint115AnalyticSupplyRecorded = true

        sprint115ClosureReducerContextText : String
        sprint115ClosureReducerContextText =
          "Sprint115 supplies residual convergence, norm gauge window control, sector stability, approximate inverse residuals, and common carrier transfer inputs for the Sprint116 reducer."

        data Sprint115ClosureReducerContextReceipt : Set where
          recorded :
            Sprint115ClosureReducerContextReceipt
        """
    )


def sprint116_fixture_module(false_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint116ClosureReducerAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        residualConvergenceReducerClosureProofFlag : Bool
        residualConvergenceReducerClosureProofFlag = {false_value}

        normGaugeWindowReducerClosureProofFlag : Bool
        normGaugeWindowReducerClosureProofFlag = {false_value}

        sectorStabilityReducerClosureProofFlag : Bool
        sectorStabilityReducerClosureProofFlag = {false_value}

        approximateInverseReducerClosureProofFlag : Bool
        approximateInverseReducerClosureProofFlag = {false_value}

        commonCarrierTransferReducerClosureProofFlag : Bool
        commonCarrierTransferReducerClosureProofFlag = {false_value}

        residualConvergenceReducerEvidenceText : String
        residualConvergenceReducerEvidenceText =
          "residual convergence reducer evidence records vanishing rates and decay from the Sprint115 residual ledger into one closure proof flag"

        normGaugeWindowReducerEvidenceText : String
        normGaugeWindowReducerEvidenceText =
          "norm gauge window reducer evidence records upper lower norm constants and gauge quotient window compatibility"

        sectorStabilityReducerEvidenceText : String
        sectorStabilityReducerEvidenceText =
          "sector stability reducer evidence records physical projection commutators, quotient descent, and vacuum sector stability"

        approximateInverseReducerEvidenceText : String
        approximateInverseReducerEvidenceText =
          "approximate inverse reducer evidence records left and right residual reductions for E_a and P_a"

        commonCarrierTransferReducerEvidenceText : String
        commonCarrierTransferReducerEvidenceText =
          "common carrier transfer reducer evidence records transfer into weak compactness, recovery convergence, and feedthrough"

        data ClosureReducerReceipt : Set where
          recorded :
            ClosureReducerReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("resid"):
            words.add("residual")
        if word.startswith("converg"):
            words.add("convergence")
        if word.startswith("reduc"):
            words.add("reducer")
        if word.startswith("stabil"):
            words.add("stability")
        if word.startswith("approxim"):
            words.add("approximate")
        if word.startswith("feed"):
            words.add("feedthrough")
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


def assert_summary_records_closure_reducer_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, RESIDUAL_CONVERGENCE_WORDS)
    assert matching_items(summary, NORM_GAUGE_WINDOW_WORDS)
    assert matching_items(summary, SECTOR_STABILITY_WORDS)
    assert matching_items(summary, APPROXIMATE_INVERSE_WORDS)
    assert matching_items(summary, COMMON_CARRIER_TRANSFER_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    for key in EVIDENCE_KEYS:
        assert summary[key], key
    assert summary["required_sprint116_closure_proof_flags"]
    assert not all(
        flag["value"] is True
        for flag in summary["required_sprint116_closure_proof_flags"]
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


def sprint115_116_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint116_fixture_summary_records_closure_reducer_audit(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 115, "ClosureReducerAuditContext", sprint115_context_module())
    write_sprint_module(tmp_path, 116, "ClosureReducerAuditFixture", sprint116_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_closure_reducer_audit(summary)
    assert summary["scanned_surfaces"]["sprint115"] == [
        "DASHI/Physics/Closure/YMSprint115ClosureReducerAuditContext.agda"
    ]
    assert summary["scanned_surfaces"]["sprint116"] == [
        "DASHI/Physics/Closure/YMSprint116ClosureReducerAuditFixture.agda"
    ]


def test_sprint116_fixture_guards_detect_placeholders_promotion_empty_data_and_metas(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    meta = "?"
    write_sprint_module(
        tmp_path,
        116,
        "ClosureReducerGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint116ClosureReducerGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            clayYangMillsPromoted : Bool
            clayYangMillsPromoted = {promoted}

            {dangerous} FutureClosureReducerLemma : Set

            unresolvedWitness : {meta}
            unresolvedWitness = {meta}

            data FutureReducerReceipt : Set where
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


def test_sprint116_all_required_true_can_pass_when_no_route_or_hard_failures(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 115, "ClosureReducerAuditContext", sprint115_context_module())
    write_sprint_module(tmp_path, 116, "ClosureReducerAuditFixture", sprint116_fixture_module("true"))

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "closure reducers proved"
    assert not summary["fail_reasons"]
    assert all(flag["value"] is True for flag in summary["required_sprint116_closure_proof_flags"])


def test_sprint115_116_real_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint115_116_modules()
    if not module_paths:
        pytest.skip("Sprint115/Sprint116 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint116_script_and_test_source_avoid_literal_placeholder_and_promotion_guards() -> None:
    for source_path in (SCRIPT, Path(__file__)):
        source = source_path.read_text()
        assert ("post" + "ulate FutureClosureReducerLemma") not in source
        assert ("clayYangMillsPromoted = " + "true") not in source


def test_sprint115_real_modules_record_closure_reducer_evidence() -> None:
    module_paths = sprint115_116_modules()
    if not module_paths:
        pytest.skip("Sprint115/Sprint116 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, RESIDUAL_CONVERGENCE_WORDS)
    assert matching_items(combined, NORM_GAUGE_WINDOW_WORDS)
    assert matching_items(combined, SECTOR_STABILITY_WORDS)
    assert matching_items(combined, APPROXIMATE_INVERSE_WORDS)
    assert matching_items(combined, COMMON_CARRIER_TRANSFER_WORDS)


def test_sprint116_real_summary_fails_closed_until_closure_flags_are_true(
    tmp_path: Path,
) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["scanned_surfaces"]["sprint115"]
    if summary["scanned_surfaces"]["sprint116"]:
        assert summary["required_sprint116_closure_proof_flags"]
        assert not all(flag["value"] is True for flag in summary["required_sprint116_closure_proof_flags"])
    else:
        assert not summary["required_sprint116_closure_proof_flags"]
    assert matching_items(summary["route_reasons"], ("sprint116", "closure", "proof"))
    for key in EVIDENCE_KEYS:
        assert summary[key], key


def test_sprint116_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 115, "ClosureReducerAuditContext", sprint115_context_module())
    write_sprint_module(tmp_path, 116, "ClosureReducerAuditFixture", sprint116_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 116 Closure-Reducer Audit" in report
    assert "Residual Convergence Reducer Evidence" in report
    assert "Norm Gauge Window Reducer Evidence" in report
    assert "Sector Stability Reducer Evidence" in report
    assert "Approximate Inverse Reducer Evidence" in report
    assert "Common Carrier Transfer Reducer Evidence" in report
    assert json_text(summary)
