from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint112_map_candidate_reduction_audit.py"
SUMMARY_NAME = "ym_sprint112_map_candidate_reduction_audit_summary.json"
REPORT_NAME = "ym_sprint112_map_candidate_reduction_audit.md"
MODULE_GLOBS = ("YMSprint111*.agda", "YMSprint112*.agda")

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

INTERPOLATION_WORDS = ("interpolation", "map", "candidate")
SAMPLING_PROJECTION_WORDS = ("sampling", "projection", "candidate")
QUOTIENT_INDEPENDENCE_WORDS = ("quotient", "independence", "diagram")
UNIFORM_NORM_BOUND_WORDS = ("uniform", "norm", "bound")
ADJOINTNESS_INVERSE_WORDS = ("adjointness", "approximate", "inverse")
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


def sprint111_context_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint111MapCandidateReductionAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        sprint111MapCandidateContextRecorded : Bool
        sprint111MapCandidateContextRecorded = true

        sprint111MapCandidateContextText : String
        sprint111MapCandidateContextText =
          "Sprint111 records finite-to-continuum embedding and projection map candidate surfaces for Sprint112 reduction."

        data Sprint111MapCandidateContextReceipt : Set where
          recorded :
            Sprint111MapCandidateContextReceipt
        """
    )


def sprint112_fixture_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint112MapCandidateReductionAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        interpolationMapCandidateReductionTheoremProvedHere : Bool
        interpolationMapCandidateReductionTheoremProvedHere = false

        samplingProjectionCandidateReductionTheoremProvedHere : Bool
        samplingProjectionCandidateReductionTheoremProvedHere = false

        quotientIndependenceDiagramReductionTheoremProvedHere : Bool
        quotientIndependenceDiagramReductionTheoremProvedHere = false

        uniformNormBoundReductionTheoremProvedHere : Bool
        uniformNormBoundReductionTheoremProvedHere = false

        adjointnessApproximateInverseReductionTheoremProvedHere : Bool
        adjointnessApproximateInverseReductionTheoremProvedHere = false

        interpolationMapCandidateEvidenceText : String
        interpolationMapCandidateEvidenceText =
          "interpolation map candidate E_a reduces finite physical quotient vectors into the continuum carrier comparison surface"

        samplingProjectionCandidateEvidenceText : String
        samplingProjectionCandidateEvidenceText =
          "sampling projection candidate P_a reduces continuum finite-energy vectors back to finite physical quotient carriers"

        quotientIndependenceDiagramEvidenceText : String
        quotientIndependenceDiagramEvidenceText =
          "quotient independence diagram evidence requires representative choices and gauge maps to commute before reduction"

        uniformNormBoundReductionEvidenceText : String
        uniformNormBoundReductionEvidenceText =
          "uniform norm bound reduction evidence records a-independent operator constants for E_a and P_a"

        adjointnessApproximateInverseReductionEvidenceText : String
        adjointnessApproximateInverseReductionEvidenceText =
          "adjointness approximate inverse reduction evidence compares E_a and P_a against identity laws after projection"

        data MapCandidateReductionReceipt : Set where
          recorded :
            MapCandidateReductionReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("interpol"):
            words.add("interpolation")
        if word.startswith("project"):
            words.add("projection")
        if word.startswith("quot"):
            words.add("quotient")
        if word.startswith("independ"):
            words.add("independence")
        if word.startswith("diagram"):
            words.add("diagram")
        if word.startswith("adjoint"):
            words.add("adjointness")
        if word.startswith("approx"):
            words.add("approximate")
        if word.startswith("reduc"):
            words.add("reduction")
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


def assert_summary_records_map_candidate_reduction_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, INTERPOLATION_WORDS)
    assert matching_items(summary, SAMPLING_PROJECTION_WORDS)
    assert matching_items(summary, QUOTIENT_INDEPENDENCE_WORDS)
    assert matching_items(summary, UNIFORM_NORM_BOUND_WORDS)
    assert matching_items(summary, ADJOINTNESS_INVERSE_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    assert summary["required_map_candidate_reduction_theorem_flags"]
    assert not all(
        flag["value"] is True
        for flag in summary["required_map_candidate_reduction_theorem_flags"]
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


def sprint111_112_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint112_fixture_summary_records_map_candidate_reduction_audit(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 111, "MapCandidateReductionAuditContext", sprint111_context_module())
    write_sprint_module(tmp_path, 112, "MapCandidateReductionAuditFixture", sprint112_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_map_candidate_reduction_audit(summary)
    assert summary["scanned_surfaces"]["sprint111"] == [
        "DASHI/Physics/Closure/YMSprint111MapCandidateReductionAuditContext.agda"
    ]
    assert summary["scanned_surfaces"]["sprint112"] == [
        "DASHI/Physics/Closure/YMSprint112MapCandidateReductionAuditFixture.agda"
    ]


def test_sprint112_fixture_guards_detect_placeholders_promotion_empty_data_and_meta(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    write_sprint_module(
        tmp_path,
        112,
        "MapCandidateReductionGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint112MapCandidateReductionGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            clayYangMillsPromoted : Bool
            clayYangMillsPromoted = {promoted}

            {dangerous} FutureLemma : Set

            unresolvedWitness = ?

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


def test_sprint111_112_real_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint111_112_modules()
    if not module_paths:
        pytest.skip("Sprint111/Sprint112 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint112_test_source_avoids_literal_placeholder_and_promotion_guards() -> None:
    source = Path(__file__).read_text()
    assert ("post" + "ulate FutureLemma") not in source
    assert ("clayYangMillsPromoted = " + "true") not in source


def test_sprint111_112_real_modules_record_required_evidence_surface() -> None:
    module_paths = sprint111_112_modules()
    if not module_paths:
        pytest.skip("Sprint111/Sprint112 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, INTERPOLATION_WORDS)
    assert matching_items(combined, SAMPLING_PROJECTION_WORDS)
    assert matching_items(combined, QUOTIENT_INDEPENDENCE_WORDS)
    assert matching_items(combined, UNIFORM_NORM_BOUND_WORDS)
    assert matching_items(combined, ADJOINTNESS_INVERSE_WORDS)


def test_sprint112_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 111, "MapCandidateReductionAuditContext", sprint111_context_module())
    write_sprint_module(tmp_path, 112, "MapCandidateReductionAuditFixture", sprint112_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 112 Map-Candidate Reduction Audit" in report
    assert "Interpolation Map Candidate Evidence" in report
    assert "Sampling Projection Candidate Evidence" in report
    assert "Quotient Independence Diagrams Evidence" in report
    assert "Uniform Norm Bound Reduction Evidence" in report
    assert "Adjointness Approximate-Inverse Reduction Evidence" in report
    assert json_text(summary)
