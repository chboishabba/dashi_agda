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
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint121_cc1_kernel_audit.py"
SUMMARY_NAME = "ym_sprint121_cc1_kernel_audit_summary.json"
MODULE_GLOBS = ("YMSprint120*.agda", "YMSprint121*.agda")
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


def run_script(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    if not SCRIPT.exists():
        pytest.skip("Sprint121 CC1 kernel audit script is not integrated yet")

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


def sprint120_context_module() -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint120CC1KernelAuditContext where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        {CLAY_NAME} : Bool
        {CLAY_NAME} = false

        sprint120SubmissionReadinessContextFlag : Bool
        sprint120SubmissionReadinessContextFlag = true

        sprint120CC1KernelContextText : String
        sprint120CC1KernelContextText =
          "Sprint120 supplies CC1 common carrier kernel inputs, external carrier certificate inputs, weak compactness certificate inputs, Mosco aggregate inputs, and transfer calculus readiness inputs."

        data Sprint120CC1KernelContextReceipt : Set where
          recorded :
            Sprint120CC1KernelContextReceipt
        """
    )


def sprint121_fixture_module(flag_value: str = "false") -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint121CC1KernelAuditFixture where

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

        cc1CommonCarrierKernelEvidenceText : String
        cc1CommonCarrierKernelEvidenceText =
          "CC1 common carrier kernel evidence records carrier construction, embedding, projection, quotient compatibility, and kernel closure."

        cc1ExternalCarrierCompatibilityEvidenceText : String
        cc1ExternalCarrierCompatibilityEvidenceText =
          "CC1 external carrier compatibility evidence records certificate feedthrough into the shared common carrier kernel."

        cc1WeakCompactnessKernelEvidenceText : String
        cc1WeakCompactnessKernelEvidenceText =
          "CC1 weak compactness kernel evidence records bounded energy subsequence extraction on the common carrier."

        cc1MoscoAggregateKernelEvidenceText : String
        cc1MoscoAggregateKernelEvidenceText =
          "CC1 Mosco aggregate kernel evidence records liminf, recovery, no pollution, no collapse, and closed form lower semicontinuity."

        cc1TransferCalculusKernelEvidenceText : String
        cc1TransferCalculusKernelEvidenceText =
          "CC1 transfer calculus kernel evidence records uniform form, log generator, spectral transport, and lower-bound readiness."

        data CC1KernelReceipt : Set where
          recorded :
            CC1KernelReceipt
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("compact"):
            words.add("compactness")
        if word.startswith("cert"):
            words.add("certificate")
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


def proof_flags(summary: dict[str, Any]) -> list[dict[str, Any]]:
    matches = [
        value
        for key, value in summary.items()
        if "flag" in key.lower()
        and isinstance(value, list)
        and all(isinstance(item, dict) and "value" in item for item in value)
    ]
    assert matches, "summary should expose required CC1 proof flags"
    return max(matches, key=len)


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


def sprint120_121_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    paths: list[Path] = []
    for glob in MODULE_GLOBS:
        paths.extend(module_dir.glob(glob))
    return sorted(paths)


def test_sprint121_cc1_fixture_fails_closed_with_false_flags(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 120, "CC1KernelAuditContext", sprint120_context_module())
    write_sprint_module(tmp_path, 121, "CC1KernelAuditFixture", sprint121_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert matching_items(summary, ("cc1", "common", "carrier", "kernel"))
    assert matching_items(summary, ("fail", "closed"))
    flags = proof_flags(summary)
    assert flags
    assert not all(flag["value"] is True for flag in flags)


def test_sprint121_cc1_fixture_passes_with_all_required_flags_true(tmp_path: Path) -> None:
    write_sprint_module(tmp_path, 120, "CC1KernelAuditContext", sprint120_context_module())
    write_sprint_module(tmp_path, 121, "CC1KernelAuditFixture", sprint121_fixture_module("true"))

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] != "fail-closed"
    assert not summary.get("fail_reasons", [])
    assert not summary.get("hard_fail_reasons", [])
    assert all(flag["value"] is True for flag in proof_flags(summary))
    assert matching_items(summary, ("cc1", "kernel"))


def test_sprint121_cc1_guards_hard_fail_on_forbidden_inputs(tmp_path: Path) -> None:
    dangerous = "post" + "ulate"
    promoted = "tr" + "ue"
    write_sprint_module(
        tmp_path,
        121,
        "CC1KernelGuardFixture",
        textwrap.dedent(
            f"""\
            module DASHI.Physics.Closure.YMSprint121CC1KernelGuardFixture where

            open import Agda.Builtin.Bool using (Bool; true)

            {CLAY_NAME} : Bool
            {CLAY_NAME} = {promoted}

            {dangerous} FutureCC1KernelLemma : Set

            unresolvedWitness : {META_CHAR}
            unresolvedWitness = {META_CHAR}

            data FutureCC1KernelReceipt : Set where
            """
        ),
    )

    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["route_decision"] == "fail-closed"
    assert summary["hard_fail_reasons"]
    assert matching_items(summary, ("promotion",)) or matching_items(summary, ("clay",))
    assert matching_items(summary, ("incomplete", "surface"))
    assert matching_items(summary, ("empty", "data"))
    assert "rhs" in json_text(summary)
    assert "type" in json_text(summary)


def test_sprint121_real_repo_scan_has_no_forbidden_markers() -> None:
    module_paths = sprint120_121_modules()
    if not module_paths:
        pytest.skip("Sprint120/Sprint121 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            if token in FORBIDDEN_WORD_PATTERNS:
                assert not FORBIDDEN_WORD_PATTERNS[token].search(text), module_path
            else:
                assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path
