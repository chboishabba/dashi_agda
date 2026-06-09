from __future__ import annotations

import json
import re
import subprocess
import sys
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint122_cc2_gauge_covariance_audit.py"
SUMMARY_NAME = "ym_sprint122_cc2_gauge_covariance_audit_summary.json"
REPORT_NAME = "ym_sprint122_cc2_gauge_covariance_audit.md"
CLAY_NAME = "clay" + "Yang" + "Mills" + "Promoted"
META_CHAR = chr(63)

pytestmark = pytest.mark.skipif(
    not SCRIPT.exists(),
    reason="Sprint122 CC2 gauge covariance audit script is not integrated yet",
)

FORBIDDEN_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
    "{" + "!",
    "!" + "}",
    "PLACE" + "HOLDER",
    "XXX",
)
FORBIDDEN_PROMOTION_TEXTS = (
    CLAY_NAME + " = " + "tr" + "ue",
    CLAY_NAME + '": ' + "tr" + "ue",
    CLAY_NAME + ": " + "tr" + "ue",
)
FORBIDDEN_WORD_PATTERNS = {
    "post" + "ulate": re.compile(r"\bpost" + "ulate\b"),
    "TO" + "DO": re.compile(r"\bTO" + "DO\b"),
    "stu" + "b": re.compile(r"\bstu" + "b\b", re.IGNORECASE),
    "PLACE" + "HOLDER": re.compile(r"\bPLACE" + "HOLDER\b", re.IGNORECASE),
}


def run_script(repo_root: Path, out_dir: Path) -> dict[str, Any]:
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
        candidates = sorted(out_dir.glob("*cc2*gauge*covariance*audit*.json"))
        assert candidates, result.stdout + result.stderr
        summary_path = candidates[0]
    return json.loads(summary_path.read_text(encoding="utf-8"))


def write_sprint_module(repo_root: Path, sprint: int, name: str, text: str) -> Path:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    path = module_dir / f"YMSprint{sprint}{name}.agda"
    path.write_text(text, encoding="utf-8")
    return path


def sprint121_cc1_context_module(flag_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint121CC2GaugeCovarianceAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        cc1CommonCarrierKernelProofFlag : Bool
        cc1CommonCarrierKernelProofFlag = {flag_value}

        cc1ExternalCarrierCompatibilityProofFlag : Bool
        cc1ExternalCarrierCompatibilityProofFlag = {flag_value}

        cc1WeakCompactnessKernelProofFlag : Bool
        cc1WeakCompactnessKernelProofFlag = {flag_value}

        cc1MoscoAggregateKernelProofFlag : Bool
        cc1MoscoAggregateKernelProofFlag = {flag_value}

        cc1TransferCalculusKernelProofFlag : Bool
        cc1TransferCalculusKernelProofFlag = {flag_value}

        sprint121CC1ContextText : String
        sprint121CC1ContextText =
          "CC1 common carrier kernel context records kernel closure, external carrier compatibility, weak compactness, Mosco aggregate, and transfer calculus inputs for the CC2 gauge covariance audit."

        data Sprint121CC1ContextReceipt : Set where
          recorded :
            Sprint121CC1ContextReceipt
        """
    )


def sprint122_cc2_fixture_module(flag_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint122CC2GaugeCovarianceAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        cc2GaugeCovarianceProofFlag : Bool
        cc2GaugeCovarianceProofFlag = {flag_value}

        cc2GaugeActionInvarianceProofFlag : Bool
        cc2GaugeActionInvarianceProofFlag = {flag_value}

        cc2GaugeTransportCompatibilityProofFlag : Bool
        cc2GaugeTransportCompatibilityProofFlag = {flag_value}

        cc2CommonCarrierGaugeCompatibilityProofFlag : Bool
        cc2CommonCarrierGaugeCompatibilityProofFlag = {flag_value}

        cc2GaugeCovarianceEvidenceText : String
        cc2GaugeCovarianceEvidenceText =
          "CC2 gauge covariance evidence records orbit compatibility, gauge action invariance, transport compatibility, and common carrier compatibility."

        cc2GaugeActionInvarianceEvidenceText : String
        cc2GaugeActionInvarianceEvidenceText =
          "CC2 gauge action invariance evidence records equivariant field action and quotient-stable observable transfer."

        cc2GaugeTransportCompatibilityEvidenceText : String
        cc2GaugeTransportCompatibilityEvidenceText =
          "CC2 gauge transport compatibility evidence records covariance through transfer calculus and spectral lower-bound transport."

        cc2CommonCarrierGaugeCompatibilityEvidenceText : String
        cc2CommonCarrierGaugeCompatibilityEvidenceText =
          "CC2 common carrier gauge compatibility evidence records compatibility with the CC1 common carrier kernel."

        data CC2GaugeCovarianceReceipt : Set where
          recorded :
            CC2GaugeCovarianceReceipt
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
        if word.startswith("covar"):
            words.add("covariance")
        if word.startswith("compat"):
            words.add("compatibility")
        if word.startswith("invar"):
            words.add("invariance")
    return words


def matching_items(value: Any, phrase: tuple[str, ...]) -> list[Any]:
    return [
        item
        for item in flatten_values(value)
        if all(word in normalized_words(item) for word in phrase)
    ]


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def proof_flags(summary: dict[str, Any]) -> list[dict[str, Any]]:
    matches = [
        value
        for key, value in summary.items()
        if "flag" in key.lower()
        and isinstance(value, list)
        and all(isinstance(item, dict) and "value" in item for item in value)
    ]
    assert matches, "summary should expose CC1/CC2 proof flags"
    flags = [flag for group in matches for flag in group]
    assert flags, "summary should include at least one proof flag"
    return flags


def promotion_flags(summary: dict[str, Any]) -> list[dict[str, Any]]:
    flags = summary.get("promotion_flags")
    assert isinstance(flags, list), "summary should expose promotion flags"
    assert flags, "summary should include at least one promotion flag"
    return flags


def output_text(out_dir: Path, summary: dict[str, Any]) -> str:
    parts = [json_text(summary)]
    for path in sorted(out_dir.glob("*")):
        if path.suffix in {".json", ".md", ".markdown", ".txt"}:
            parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(parts)


def assert_no_forbidden_markers(text: str) -> None:
    for token in FORBIDDEN_TOKENS:
        if token in FORBIDDEN_WORD_PATTERNS:
            assert not FORBIDDEN_WORD_PATTERNS[token].search(text), token
        else:
            assert token not in text
    for promotion in FORBIDDEN_PROMOTION_TEXTS:
        assert promotion not in text


def test_sprint122_cc2_fixture_fails_closed_until_cc1_and_cc2_flags_are_proved(
    tmp_path: Path,
) -> None:
    write_sprint_module(tmp_path, 121, "CC2GaugeCovarianceAuditContext", sprint121_cc1_context_module())
    write_sprint_module(tmp_path, 122, "CC2GaugeCovarianceAuditFixture", sprint122_cc2_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, ("cc1",))
    assert matching_items(summary, ("cc2", "gauge", "covariance"))
    assert matching_items(summary, ("fail", "closed"))
    assert not all(flag["value"] is True for flag in proof_flags(summary))


def test_sprint122_cc2_cli_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 121, "CC2GaugeCovarianceAuditContext", sprint121_cc1_context_module())
    write_sprint_module(tmp_path, 122, "CC2GaugeCovarianceAuditFixture", sprint122_cc2_fixture_module())

    summary = run_script(tmp_path, out_dir)
    report_path = out_dir / REPORT_NAME
    if not report_path.exists():
        candidates = sorted(out_dir.glob("*cc2*gauge*covariance*audit*.md"))
        assert candidates
        report_path = candidates[0]

    report = report_path.read_text(encoding="utf-8")
    assert "Sprint 122" in report or "Sprint122" in report
    assert "CC2" in report
    assert "Gauge" in report
    assert "Covariance" in report
    assert "fail-closed" in output_text(out_dir, summary)


def test_sprint122_cc2_outputs_remain_non_promoting_and_marker_free(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    write_sprint_module(tmp_path, 121, "CC2GaugeCovarianceAuditContext", sprint121_cc1_context_module())
    write_sprint_module(tmp_path, 122, "CC2GaugeCovarianceAuditFixture", sprint122_cc2_fixture_module())

    summary = run_script(tmp_path, out_dir)

    assert_no_forbidden_markers(output_text(out_dir, summary))
    assert all(flag["value"] is False for flag in promotion_flags(summary))


def test_sprint122_cc2_guard_rejects_markers_and_promotion(tmp_path: Path) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    write_sprint_module(
        tmp_path,
        122,
        "CC2GaugeCovarianceGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint122CC2GaugeCovarianceGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            {CLAY_NAME} : Bool
            {CLAY_NAME} = {promoted}

            {dangerous} FutureCC2GaugeCovarianceLemma : Set

            unresolvedWitness : {META_CHAR}
            unresolvedWitness = {META_CHAR}

            data FutureCC2GaugeCovarianceReceipt : Set where
            """
        ),
    )

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, ("promotion",)) or matching_items(summary, ("clay",))
    assert matching_items(summary, ("incomplete",)) or matching_items(summary, ("unresolved",))


def test_sprint122_cc2_real_repo_summary_is_fail_closed_and_non_promoting(
    tmp_path: Path,
) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")
    text = output_text(tmp_path / "out", summary)

    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, ("cc1",))
    assert matching_items(summary, ("cc2", "gauge", "covariance"))
    assert not all(flag["value"] is True for flag in proof_flags(summary))
    assert_no_forbidden_markers(text)
