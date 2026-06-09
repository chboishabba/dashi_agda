from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint111_common_carrier_construction_audit.py"
SUMMARY_NAME = "ym_sprint111_common_carrier_construction_audit_summary.json"
REPORT_NAME = "ym_sprint111_common_carrier_construction_audit.md"
MODULE_GLOBS = ("YMSprint110*.agda", "YMSprint111*.agda")

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

EMBEDDING_PROJECTION_WORDS = ("embedding", "projection")
GAUGE_QUOTIENT_WORDS = ("gauge", "quotient")
UNIFORM_NORM_WORDS = ("uniform", "norm")
ADJOINTNESS_STABILITY_WORDS = ("adjointness", "stability")
CONSTRUCTION_ASSEMBLY_WORDS = ("construction", "assembly")
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


def sprint110_context_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint110CommonCarrierConstructionAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        embeddingProjectionSurfacesRecorded : Bool
        embeddingProjectionSurfacesRecorded = true

        sprint110ContextText : String
        sprint110ContextText =
          "Sprint110 records common carrier embedding and projection surfaces for the physical gauge quotient."

        data Sprint110ConstructionContextReceipt : Set where
          recorded :
            Sprint110ConstructionContextReceipt
        """
    )


def sprint111_fixture_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint111CommonCarrierConstructionAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        embeddingProjectionMapsConstructedHere : Bool
        embeddingProjectionMapsConstructedHere = false

        gaugeQuotientPhysicalSectorConstructedHere : Bool
        gaugeQuotientPhysicalSectorConstructedHere = false

        uniformNormWindowTheoremProvedHere : Bool
        uniformNormWindowTheoremProvedHere = false

        adjointnessProjectionStabilityTheoremProvedHere : Bool
        adjointnessProjectionStabilityTheoremProvedHere = false

        commonCarrierConstructionAssemblyTheoremProvedHere : Bool
        commonCarrierConstructionAssemblyTheoremProvedHere = false

        embeddingProjectionMapsEvidenceText : String
        embeddingProjectionMapsEvidenceText =
          "embedding and projection maps E_a and P_a connect finite carriers with the continuum physical carrier"

        gaugeQuotientPhysicalSectorEvidenceText : String
        gaugeQuotientPhysicalSectorEvidenceText =
          "gauge quotient physical sector evidence removes representative choices before comparing carriers"

        uniformNormWindowEvidenceText : String
        uniformNormWindowEvidenceText =
          "uniform norm window evidence records admissible spacing constants for carrier equivalence"

        adjointnessProjectionStabilityEvidenceText : String
        adjointnessProjectionStabilityEvidenceText =
          "adjointness and projection stability evidence controls approximate inverse laws in physical norms"

        commonCarrierConstructionAssemblyEvidenceText : String
        commonCarrierConstructionAssemblyEvidenceText =
          "common carrier construction assembly evidence packages maps quotient sector norm window and stability"

        data CommonCarrierConstructionReceipt : Set where
          recorded :
            CommonCarrierConstructionReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("embed"):
            words.add("embedding")
        if word.startswith("project"):
            words.add("projection")
        if word.startswith("quot"):
            words.add("quotient")
        if word.startswith("construct"):
            words.add("construction")
        if word.startswith("adjoint"):
            words.add("adjointness")
        if word.startswith("stabil"):
            words.add("stability")
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


def assert_summary_records_common_carrier_construction_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, EMBEDDING_PROJECTION_WORDS)
    assert matching_items(summary, GAUGE_QUOTIENT_WORDS)
    assert matching_items(summary, UNIFORM_NORM_WORDS)
    assert matching_items(summary, ADJOINTNESS_STABILITY_WORDS)
    assert matching_items(summary, CONSTRUCTION_ASSEMBLY_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    assert summary["required_common_carrier_construction_theorem_flags"]
    assert not all(
        flag["value"] is True
        for flag in summary["required_common_carrier_construction_theorem_flags"]
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


def sprint110_111_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint111_fixture_summary_records_common_carrier_construction_audit(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 110, "CommonCarrierConstructionAuditContext", sprint110_context_module())
    write_sprint_module(tmp_path, 111, "CommonCarrierConstructionAuditFixture", sprint111_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_common_carrier_construction_audit(summary)
    assert summary["scanned_surfaces"]["sprint110"] == [
        "DASHI/Physics/Closure/YMSprint110CommonCarrierConstructionAuditContext.agda"
    ]
    assert summary["scanned_surfaces"]["sprint111"] == [
        "DASHI/Physics/Closure/YMSprint111CommonCarrierConstructionAuditFixture.agda"
    ]


def test_sprint111_fixture_guards_detect_placeholders_promotion_empty_data_and_meta(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    write_sprint_module(
        tmp_path,
        111,
        "CommonCarrierConstructionGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint111CommonCarrierConstructionGuardFixture where

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


def test_sprint110_111_real_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint110_111_modules()
    if not module_paths:
        pytest.skip("Sprint110/Sprint111 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint111_test_source_avoids_literal_placeholder_and_promotion_guards() -> None:
    source = Path(__file__).read_text()
    assert ("post" + "ulate FutureLemma") not in source
    assert ("clayYangMillsPromoted = " + "true") not in source


def test_sprint110_111_real_modules_record_required_evidence_surface() -> None:
    module_paths = sprint110_111_modules()
    if not module_paths:
        pytest.skip("Sprint110/Sprint111 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, EMBEDDING_PROJECTION_WORDS)
    assert matching_items(combined, GAUGE_QUOTIENT_WORDS)
    assert matching_items(combined, UNIFORM_NORM_WORDS)
    assert matching_items(combined, ADJOINTNESS_STABILITY_WORDS)
    assert matching_items(combined, CONSTRUCTION_ASSEMBLY_WORDS)


def test_sprint111_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 110, "CommonCarrierConstructionAuditContext", sprint110_context_module())
    write_sprint_module(tmp_path, 111, "CommonCarrierConstructionAuditFixture", sprint111_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 111 Common Carrier Construction Audit" in report
    assert "Embedding/Projection Maps Evidence" in report
    assert "Gauge Quotient Physical Sector Evidence" in report
    assert "Uniform Norm Window Evidence" in report
    assert "Adjointness/Projection Stability Evidence" in report
    assert "Common Carrier Construction Assembly Evidence" in report
    assert json_text(summary)
