from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint120_certificate_audit.py"
SUMMARY_NAME = "ym_sprint120_certificate_audit_summary.json"
REPORT_NAME = "ym_sprint120_certificate_audit.md"
MODULE_GLOBS = ("YMSprint119*.agda", "YMSprint120*.agda")
CLAY_NAME = "clay" + "Yang" + "Mills" + "Promoted"
META_CHAR = chr(63)

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
    "external_common_carrier_certificate_evidence",
    "weak_compactness_certificate_evidence",
    "common_carrier_feedthrough_closure_reducer_evidence",
    "mosco_aggregate_certificate_evidence",
    "transfer_calculus_certificate_evidence",
)
EXTERNAL_COMMON_WORDS = ("external", "common", "carrier", "certificate")
WEAK_COMPACTNESS_WORDS = ("weak", "compactness", "certificate")
FEEDTHROUGH_CLOSURE_WORDS = ("common", "carrier", "feedthrough", "closure", "reducer")
MOSCO_AGGREGATE_WORDS = ("mosco", "aggregate", "certificate")
TRANSFER_CALCULUS_WORDS = ("transfer", "calculus", "certificate")
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


def sprint119_context_module() -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint119CertificateAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        sprint119CertificateContextFlag : Bool
        sprint119CertificateContextFlag = true

        sprint119CertificateContextText : String
        sprint119CertificateContextText =
          "Sprint119 supplies external common carrier certificate inputs, weak compactness certificate inputs, common carrier feedthrough closure reducer inputs, Mosco aggregate certificate inputs, and transfer calculus certificate inputs."

        data Sprint119CertificateContextReceipt : Set where
          recorded :
            Sprint119CertificateContextReceipt
        """
    )


def sprint120_fixture_module(false_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint120CertificateAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        externalCommonCarrierCertificateProofFlag : Bool
        externalCommonCarrierCertificateProofFlag = {false_value}

        weakCompactnessCertificateProofFlag : Bool
        weakCompactnessCertificateProofFlag = {false_value}

        commonCarrierFeedthroughClosureReducerProofFlag : Bool
        commonCarrierFeedthroughClosureReducerProofFlag = {false_value}

        moscoAggregateCertificateProofFlag : Bool
        moscoAggregateCertificateProofFlag = {false_value}

        transferCalculusCertificateProofFlag : Bool
        transferCalculusCertificateProofFlag = {false_value}

        externalCommonCarrierCertificateEvidenceText : String
        externalCommonCarrierCertificateEvidenceText =
          "external common carrier certificate evidence records construction, embedding, projection, and quotient compatibility"

        weakCompactnessCertificateEvidenceText : String
        weakCompactnessCertificateEvidenceText =
          "weak compactness certificate evidence records bounded energy subsequence extraction on the common carrier"

        commonCarrierFeedthroughClosureReducerEvidenceText : String
        commonCarrierFeedthroughClosureReducerEvidenceText =
          "common carrier feedthrough closure reducer evidence records criterion feed-through closure and construction"

        moscoAggregateCertificateEvidenceText : String
        moscoAggregateCertificateEvidenceText =
          "Mosco aggregate certificate evidence records liminf, recovery, no pollution, no collapse, and closed form LSC"

        transferCalculusCertificateEvidenceText : String
        transferCalculusCertificateEvidenceText =
          "transfer calculus certificate evidence records uniform form, log generator, spectral transport, and lower-bound readiness"

        data CertificateReceipt : Set where
          recorded :
            CertificateReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("compact"):
            words.add("compactness")
        if word.startswith("cert"):
            words.add("certificate")
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


def assert_summary_records_certificate_audit(summary: dict[str, Any]) -> None:
    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, EXTERNAL_COMMON_WORDS)
    assert matching_items(summary, WEAK_COMPACTNESS_WORDS)
    assert matching_items(summary, FEEDTHROUGH_CLOSURE_WORDS)
    assert matching_items(summary, MOSCO_AGGREGATE_WORDS)
    assert matching_items(summary, TRANSFER_CALCULUS_WORDS)
    assert matching_items(summary, FAIL_CLOSED_WORDS)
    for key in EVIDENCE_KEYS:
        assert summary[key], key
    flags = summary["required_sprint120_certificate_closure_proof_flags"]
    assert flags
    assert not all(flag["value"] is True for flag in flags)


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


def sprint119_120_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint120_fixture_summary_fails_closed_until_certificate_flags_true(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 119, "CertificateAuditContext", sprint119_context_module())
    write_sprint_module(tmp_path, 120, "CertificateAuditFixture", sprint120_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_certificate_audit(summary)
    assert summary["scanned_surfaces"]["sprint119"] == [
        "DASHI/Physics/Closure/YMSprint119CertificateAuditContext.agda"
    ]
    assert summary["scanned_surfaces"]["sprint120"] == [
        "DASHI/Physics/Closure/YMSprint120CertificateAuditFixture.agda"
    ]


def test_sprint120_fixture_guards_detect_markers_promotion_empty_data_and_unresolved(
    tmp_path: Path,
) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    write_sprint_module(
        tmp_path,
        120,
        "CertificateGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint120CertificateGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            {CLAY_NAME} : Bool
            {CLAY_NAME} = {promoted}

            {dangerous} FutureCertificateLemma : Set

            unresolvedWitness : {META_CHAR}
            unresolvedWitness = {META_CHAR}

            data FutureCertificateReceipt : Set where
            """
        ),
    )

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["hard_fail_reasons"]
    assert matching_items(summary, ("promotion",)) or matching_items(summary, ("clay",))
    assert matching_items(summary, ("incomplete", "surface"))
    assert matching_items(summary, ("empty", "data"))
    assert "rhs-unresolved" in json_text(summary)
    assert "type-unresolved" in json_text(summary)


def test_sprint120_all_required_true_can_pass_when_no_route_or_hard_failures(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 119, "CertificateAuditContext", sprint119_context_module())
    write_sprint_module(tmp_path, 120, "CertificateAuditFixture", sprint120_fixture_module("true"))

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "sprint120 certificate route proved"
    assert not summary["fail_reasons"]
    assert all(flag["value"] is True for flag in summary["required_sprint120_certificate_closure_proof_flags"])


def test_sprint119_120_real_modules_have_no_markers_empty_data_or_promotion() -> None:
    module_paths = sprint119_120_modules()
    if not module_paths:
        pytest.skip("Sprint119/Sprint120 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint120_script_and_test_source_avoid_literal_guard_triggers() -> None:
    for source_path in (SCRIPT, Path(__file__)):
        source = source_path.read_text()
        assert ("post" + "ulate FutureCertificateLemma") not in source
        assert ("TO" + "DO") not in source
        assert ("stu" + "b") not in source.lower()
        assert ("{" + "!") not in source
        assert ("!" + "}") not in source
        assert (CLAY_NAME + " = " + "tr" + "ue") not in source
        assert " : " + META_CHAR not in source
        assert " = " + META_CHAR not in source


def test_sprint119_real_modules_record_certificate_input_evidence() -> None:
    module_paths = sprint119_120_modules()
    if not module_paths:
        pytest.skip("Sprint119/Sprint120 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert matching_items(combined, ("common", "carrier"))
    assert matching_items(combined, ("weak", "compactness"))
    assert matching_items(combined, ("mosco",))
    assert matching_items(combined, ("transfer", "calculus"))


def test_sprint120_real_summary_shape_is_fail_closed(tmp_path: Path) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["scanned_surfaces"]["sprint119"]
    assert "sprint120" in summary["scanned_surfaces"]
    assert "required_sprint120_certificate_closure_proof_flags" in summary
    assert matching_items(summary["route_reasons"], ("sprint120",))
    for key in EVIDENCE_KEYS:
        assert key in summary


def test_sprint120_cli_writes_json_and_markdown(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 119, "CertificateAuditContext", sprint119_context_module())
    write_sprint_module(tmp_path, 120, "CertificateAuditFixture", sprint120_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    report_path = tmp_path / "out" / REPORT_NAME

    assert summary["route_decision"] == "fail-closed"
    assert report_path.exists()
    report = report_path.read_text()
    assert "YM Sprint 120 Certificate Audit" in report
    assert "External Common Carrier Certificate Evidence" in report
    assert "Weak Compactness Certificate Evidence" in report
    assert "Common Carrier Feedthrough Closure Reducer Evidence" in report
    assert "Mosco Aggregate Certificate Evidence" in report
    assert "Transfer Calculus Certificate Evidence" in report
    assert json_text(summary)
