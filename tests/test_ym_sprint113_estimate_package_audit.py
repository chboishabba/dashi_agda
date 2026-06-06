from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint113_estimate_package_audit.py"
SUMMARY_NAME = "ym_sprint113_estimate_package_audit_summary.json"
REPORT_NAME = "ym_sprint113_estimate_package_audit.md"
MODULE_GLOBS = ("YMSprint112*.agda", "YMSprint113*.agda")

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

GAUGE_SECTION_WORDS = ("gauge", "covariance", "section")
JACOBIAN_PARTITION_WORDS = ("jacobian", "partition")
QUOTIENT_NORM_WORDS = ("quotient", "norm", "comparison")
QUADRATURE_RESIDUAL_WORDS = ("quadrature", "residual")
INVERSE_PROJECTION_WORDS = ("inverse", "projection", "residual")
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


def sprint112_context_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint112EstimatePackageAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        sprint112EstimateReductionRecorded : Bool
        sprint112EstimateReductionRecorded = true

        sprint112EstimateContextText : String
        sprint112EstimateContextText =
          "Sprint112 reduces E_a/P_a estimates to gauge local section, Jacobian partition, quotient norm, quadrature residual, and inverse projection residual obligations."

        data Sprint112EstimateContextReceipt : Set where
          recorded :
            Sprint112EstimateContextReceipt
        """
    )


def sprint113_fixture_module(false_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint113EstimatePackageAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        gaugeCovarianceLocalSectionEstimateTheoremProvedHere : Bool
        gaugeCovarianceLocalSectionEstimateTheoremProvedHere = {false_value}

        localJacobianPartitionEstimateTheoremProvedHere : Bool
        localJacobianPartitionEstimateTheoremProvedHere = {false_value}

        quotientNormComparisonEstimateTheoremProvedHere : Bool
        quotientNormComparisonEstimateTheoremProvedHere = {false_value}

        quadratureResidualEstimateTheoremProvedHere : Bool
        quadratureResidualEstimateTheoremProvedHere = {false_value}

        inverseProjectionResidualAssemblyTheoremProvedHere : Bool
        inverseProjectionResidualAssemblyTheoremProvedHere = {false_value}

        gaugeCovarianceLocalSectionEvidenceText : String
        gaugeCovarianceLocalSectionEvidenceText =
          "gauge covariance local section evidence records representative-independent section choices for the E_a and P_a comparison maps"

        localJacobianPartitionEvidenceText : String
        localJacobianPartitionEvidenceText =
          "local Jacobian partition evidence records chart Jacobian bounds and partition multiplicity constants"

        quotientNormComparisonEvidenceText : String
        quotientNormComparisonEvidenceText =
          "quotient norm comparison evidence records representative-invariant constants between finite quotient and continuum physical norms"

        quadratureResidualEvidenceText : String
        quadratureResidualEvidenceText =
          "quadrature residual evidence records inner-product residual estimates for adjointness of E_a and P_a"

        inverseProjectionResidualAssemblyEvidenceText : String
        inverseProjectionResidualAssemblyEvidenceText =
          "inverse projection residual assembly evidence records left inverse, right inverse, and physical projection stability residual bounds"

        data EstimatePackageReceipt : Set where
          recorded :
            EstimatePackageReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("covarian"):
            words.add("covariance")
        if word.startswith("jacob"):
            words.add("jacobian")
        if word.startswith("partit"):
            words.add("partition")
        if word.startswith("quot"):
            words.add("quotient")
        if word.startswith("compar"):
            words.add("comparison")
        if word.startswith("quad"):
            words.add("quadrature")
        if word.startswith("resid"):
            words.add("residual")
        if word.startswith("project"):
            words.add("projection")
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


def assert_summary_records_estimate_package_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, GAUGE_SECTION_WORDS)
    assert matching_items(summary, JACOBIAN_PARTITION_WORDS)
    assert matching_items(summary, QUOTIENT_NORM_WORDS)
    assert matching_items(summary, QUADRATURE_RESIDUAL_WORDS)
    assert matching_items(summary, INVERSE_PROJECTION_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    assert summary["required_estimate_package_theorem_flags"]
    assert not all(
        flag["value"] is True
        for flag in summary["required_estimate_package_theorem_flags"]
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


def sprint112_113_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint113_fixture_summary_records_estimate_package_audit(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 112, "EstimatePackageAuditContext", sprint112_context_module())
    write_sprint_module(tmp_path, 113, "EstimatePackageAuditFixture", sprint113_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_estimate_package_audit(summary)
    assert summary["scanned_surfaces"]["sprint112"] == [
        "DASHI/Physics/Closure/YMSprint112EstimatePackageAuditContext.agda"
    ]
    assert summary["scanned_surfaces"]["sprint113"] == [
        "DASHI/Physics/Closure/YMSprint113EstimatePackageAuditFixture.agda"
    ]


def test_sprint113_fixture_guards_detect_placeholders_promotion_empty_data_and_meta(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    rhs_meta = "?"
    write_sprint_module(
        tmp_path,
        113,
        "EstimatePackageGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint113EstimatePackageGuardFixture where

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


def test_sprint113_all_required_true_can_pass_when_no_route_or_hard_failures(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 112, "EstimatePackageAuditContext", sprint112_context_module())
    write_sprint_module(tmp_path, 113, "EstimatePackageAuditFixture", sprint113_fixture_module("true"))

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "estimate package theorem proved"
    assert not summary["fail_reasons"]
    assert all(flag["value"] is True for flag in summary["required_estimate_package_theorem_flags"])


def test_sprint112_113_real_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint112_113_modules()
    if not module_paths:
        pytest.skip("Sprint112/Sprint113 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint113_test_source_avoids_literal_placeholder_and_promotion_guards() -> None:
    source = Path(__file__).read_text()
    assert ("post" + "ulate FutureLemma") not in source
    assert ("clayYangMillsPromoted = " + "true") not in source


def test_sprint112_real_modules_record_required_estimate_surfaces() -> None:
    module_paths = sprint112_113_modules()
    if not module_paths:
        pytest.skip("Sprint112/Sprint113 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, GAUGE_SECTION_WORDS)
    assert matching_items(combined, JACOBIAN_PARTITION_WORDS)
    assert matching_items(combined, QUOTIENT_NORM_WORDS)
    assert matching_items(combined, QUADRATURE_RESIDUAL_WORDS)
    assert matching_items(combined, INVERSE_PROJECTION_WORDS)


def test_sprint113_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 112, "EstimatePackageAuditContext", sprint112_context_module())
    write_sprint_module(tmp_path, 113, "EstimatePackageAuditFixture", sprint113_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 113 Estimate-Package Audit" in report
    assert "Gauge Covariance Local Section Evidence" in report
    assert "Local Jacobian Partition Evidence" in report
    assert "Quotient Norm Comparison Evidence" in report
    assert "Quadrature Residual Evidence" in report
    assert "Inverse Projection Residual Assembly Evidence" in report
    assert json_text(summary)
