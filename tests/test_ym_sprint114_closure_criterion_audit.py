from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint114_closure_criterion_audit.py"
SUMMARY_NAME = "ym_sprint114_closure_criterion_audit_summary.json"
REPORT_NAME = "ym_sprint114_closure_criterion_audit.md"
MODULE_GLOBS = ("YMSprint113*.agda", "YMSprint114*.agda")

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

GAUGE_QUOTIENT_WORDS = ("gauge", "quotient", "closure")
UNIFORM_NORM_WORDS = ("uniform", "norm", "constant")
QUADRATURE_RESIDUAL_WORDS = ("quadrature", "residual", "closure")
INVERSE_PROJECTION_WORDS = ("inverse", "projection", "closure")
COMMON_CARRIER_WORDS = ("common", "carrier", "estimate")
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


def sprint113_context_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint113ClosureCriterionAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        sprint113EstimatePackageRecorded : Bool
        sprint113EstimatePackageRecorded = true

        sprint113ClosureCriterionContextText : String
        sprint113ClosureCriterionContextText =
          "Sprint113 supplies gauge quotient, uniform norm, quadrature residual, inverse projection, and common carrier estimate inputs for Sprint114 closure criteria."

        data Sprint113ClosureCriterionContextReceipt : Set where
          recorded :
            Sprint113ClosureCriterionContextReceipt
        """
    )


def sprint114_fixture_module(false_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint114ClosureCriterionAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        gaugeQuotientClosureCriterionProvedHere : Bool
        gaugeQuotientClosureCriterionProvedHere = {false_value}

        uniformNormConstantAssemblyClosedHere : Bool
        uniformNormConstantAssemblyClosedHere = {false_value}

        quadratureResidualClosureCriterionProvedHere : Bool
        quadratureResidualClosureCriterionProvedHere = {false_value}

        inverseProjectionClosureCriterionProvedHere : Bool
        inverseProjectionClosureCriterionProvedHere = {false_value}

        commonCarrierEstimateClosureAssemblyClosedHere : Bool
        commonCarrierEstimateClosureAssemblyClosedHere = {false_value}

        gaugeQuotientClosureCriterionEvidenceText : String
        gaugeQuotientClosureCriterionEvidenceText =
          "gauge quotient closure criterion evidence records representative independence, descent, and physical projection compatibility"

        uniformNormConstantAssemblyEvidenceText : String
        uniformNormConstantAssemblyEvidenceText =
          "uniform norm constant assembly evidence records one cutoff independent comparison window and constants for E_a and P_a"

        quadratureResidualClosureCriterionEvidenceText : String
        quadratureResidualClosureCriterionEvidenceText =
          "quadrature residual closure criterion evidence records inner product residual vanishing conditions for adjointness"

        inverseProjectionClosureCriterionEvidenceText : String
        inverseProjectionClosureCriterionEvidenceText =
          "inverse projection closure criterion evidence records left inverse, right inverse, and projection stability closure"

        commonCarrierEstimateClosureAssemblyEvidenceText : String
        commonCarrierEstimateClosureAssemblyEvidenceText =
          "common carrier estimate closure assembly evidence records feed through from estimate closure into the common carrier construction"

        data ClosureCriterionReceipt : Set where
          recorded :
            ClosureCriterionReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("quot"):
            words.add("quotient")
        if word.startswith("clos"):
            words.add("closure")
        if word.startswith("criter"):
            words.add("criterion")
        if word.startswith("quad"):
            words.add("quadrature")
        if word.startswith("resid"):
            words.add("residual")
        if word.startswith("project"):
            words.add("projection")
        if word.startswith("const"):
            words.add("constant")
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


def assert_summary_records_closure_criterion_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, GAUGE_QUOTIENT_WORDS)
    assert matching_items(summary, UNIFORM_NORM_WORDS)
    assert matching_items(summary, QUADRATURE_RESIDUAL_WORDS)
    assert matching_items(summary, INVERSE_PROJECTION_WORDS)
    assert matching_items(summary, COMMON_CARRIER_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    assert summary["required_sprint114_closure_proof_flags"]
    assert not all(
        flag["value"] is True
        for flag in summary["required_sprint114_closure_proof_flags"]
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


def sprint113_114_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint114_fixture_summary_records_closure_criterion_audit(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 113, "ClosureCriterionAuditContext", sprint113_context_module())
    write_sprint_module(tmp_path, 114, "ClosureCriterionAuditFixture", sprint114_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_closure_criterion_audit(summary)
    assert summary["scanned_surfaces"]["sprint113"] == [
        "DASHI/Physics/Closure/YMSprint113ClosureCriterionAuditContext.agda"
    ]
    assert summary["scanned_surfaces"]["sprint114"] == [
        "DASHI/Physics/Closure/YMSprint114ClosureCriterionAuditFixture.agda"
    ]


def test_sprint114_fixture_guards_detect_placeholders_promotion_empty_data_and_meta(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    rhs_meta = "?"
    write_sprint_module(
        tmp_path,
        114,
        "ClosureCriterionGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint114ClosureCriterionGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            clayYangMillsPromoted : Bool
            clayYangMillsPromoted = {promoted}

            {dangerous} FutureLemma : Set

            unresolvedWitness = {rhs_meta}

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
    assert "rhs-meta" in json_text(summary)


def test_sprint114_all_required_true_can_pass_when_no_route_or_hard_failures(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 113, "ClosureCriterionAuditContext", sprint113_context_module())
    write_sprint_module(tmp_path, 114, "ClosureCriterionAuditFixture", sprint114_fixture_module("true"))

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "closure criterion proved"
    assert not summary["fail_reasons"]
    assert all(flag["value"] is True for flag in summary["required_sprint114_closure_proof_flags"])


def test_sprint113_114_real_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint113_114_modules()
    if not module_paths:
        pytest.skip("Sprint113/Sprint114 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint114_test_source_avoids_literal_placeholder_and_promotion_guards() -> None:
    source = Path(__file__).read_text()
    assert ("post" + "ulate FutureLemma") not in source
    assert ("clayYangMillsPromoted = " + "true") not in source


def test_sprint113_real_modules_record_closure_criterion_inputs() -> None:
    module_paths = sprint113_114_modules()
    if not module_paths:
        pytest.skip("Sprint113/Sprint114 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, GAUGE_QUOTIENT_WORDS)
    assert matching_items(combined, UNIFORM_NORM_WORDS)
    assert matching_items(combined, QUADRATURE_RESIDUAL_WORDS)
    assert matching_items(combined, INVERSE_PROJECTION_WORDS)
    assert matching_items(combined, COMMON_CARRIER_WORDS)


def test_sprint114_real_summary_fails_closed_until_closure_flags_are_all_true(
    tmp_path: Path,
) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["scanned_surfaces"]["sprint113"]
    assert summary["scanned_surfaces"]["sprint114"]
    assert summary["required_sprint114_closure_proof_flags"]
    assert not all(flag["value"] is True for flag in summary["required_sprint114_closure_proof_flags"])
    assert matching_items(summary["route_reasons"], ("sprint114", "closure", "proof", "flags"))


def test_sprint114_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 113, "ClosureCriterionAuditContext", sprint113_context_module())
    write_sprint_module(tmp_path, 114, "ClosureCriterionAuditFixture", sprint114_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 114 Closure-Criterion Audit" in report
    assert "Gauge Quotient Closure Criterion Evidence" in report
    assert "Uniform Norm Constant Assembly Evidence" in report
    assert "Quadrature Residual Closure Criterion Evidence" in report
    assert "Inverse Projection Closure Criterion Evidence" in report
    assert "Common Carrier Estimate Closure Assembly Evidence" in report
    assert json_text(summary)
