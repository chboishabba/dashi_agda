from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint108_transfer_lower_bound_audit.py"
SUMMARY_NAME = "ym_sprint108_transfer_lower_bound_audit_summary.json"
MODULE_GLOB = "YMSprint108*.agda"

TRANSFER_GAP_TARGET = "gap(T(a)) >= c * m_eff(a) * a"
FORBIDDEN_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
    "{" + "!" + "!" + "}",
    "{" + "!",
    "!" + "}",
)
FORBIDDEN_PROMOTION = "clayYangMillsPromoted = " + "true"

TARGET_WORDS = ("gap", "t", "a", "c", "m", "eff")
MOSCO_NO_POLLUTION_WORDS = ("mosco", "pollution", "evidence")
LOG_GENERATOR_WORDS = ("log", "generator", "evidence")
UNIFORM_FORM_LOWER_BOUND_WORDS = ("uniform", "form", "lower", "bound", "evidence")
SPECTRAL_TRANSPORT_WORDS = ("spectral", "transport", "evidence")
OPEN_THEOREM_WORDS = ("theorem", "open")
PROVED_THEOREM_WORDS = ("theorem", "proved")

MODULE_MOSCO_NO_POLLUTION_WORDS = ("mosco", "pollution")
MODULE_LOG_GENERATOR_WORDS = ("log", "generator")
MODULE_UNIFORM_FORM_LOWER_BOUND_WORDS = ("uniform", "form", "lower", "bound")
MODULE_SPECTRAL_TRANSPORT_WORDS = ("spectral", "transport")


def run_script(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    if not SCRIPT.exists():
        pytest.skip("Sprint108 transfer lower-bound audit script is not integrated yet")

    subprocess.run(
        [
            "python",
            str(SCRIPT),
            "--repo-root",
            str(repo_root),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    summary_path = out_dir / SUMMARY_NAME
    if not summary_path.exists():
        candidates = sorted(out_dir.glob("*summary*.json"))
        assert candidates, f"no summary JSON written under {out_dir}"
        summary_path = candidates[0]
    return json.loads(summary_path.read_text())


def write_sprint108_module(repo_root: Path, name: str, text: str) -> None:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    (module_dir / f"YMSprint108{name}.agda").write_text(text)


def sprint108_fixture_module() -> str:
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint108TransferLowerBoundAuditFixture where

        open import Agda.Builtin.Bool using (Bool; false)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        transferLowerBoundTarget : String
        transferLowerBoundTarget =
          "{TRANSFER_GAP_TARGET}"

        moscoNoPollutionEvidence : String
        moscoNoPollutionEvidence =
          "Mosco convergence and no-pollution evidence protect the transfer target"

        logGeneratorEvidence : String
        logGeneratorEvidence =
          "log-generator evidence extracts the generator lower-bound comparison"

        uniformFormLowerBoundEvidence : String
        uniformFormLowerBoundEvidence =
          "uniform form lower-bound evidence records c * m_eff(a) with scale control"

        spectralTransportEvidence : String
        spectralTransportEvidence =
          "spectral transport evidence carries the form bound to gap(T(a))"

        theoremClosureStatus : String
        theoremClosureStatus =
          "theorem remains open unless explicitly proved"
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word == "meff":
            words.update({"m", "eff"})
        if word.startswith("logarithm"):
            words.add("log")
        if word.startswith("generat"):
            words.add("generator")
        if word.startswith("evid"):
            words.add("evidence")
        if word.startswith("pollut"):
            words.add("pollution")
        if word.startswith("spectr"):
            words.add("spectral")
        if word.startswith("transp"):
            words.add("transport")
        if word.startswith(("bridg", "passage", "carry")):
            words.add("transport")
    return words


def flatten_values(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [
            nested for item in value.values() for nested in flatten_values(item)
        ]
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


def theorem_explicitly_proved(value: Any) -> bool:
    for item in flatten_values(value):
        item_words = normalized_words(item)
        item_text = json.dumps(item).lower()
        if all(word in item_words for word in PROVED_THEOREM_WORDS):
            if "not proved" not in item_text and "unproved" not in item_text:
                return True
    return False


def assert_summary_records_transfer_lower_bound_audit(summary: dict[str, Any]) -> None:
    serialized = json_text(summary)

    assert TRANSFER_GAP_TARGET in serialized or matching_items(summary, TARGET_WORDS)
    assert matching_items(summary, MOSCO_NO_POLLUTION_WORDS)
    assert matching_items(summary, LOG_GENERATOR_WORDS)
    assert matching_items(summary, UNIFORM_FORM_LOWER_BOUND_WORDS)
    assert matching_items(summary, SPECTRAL_TRANSPORT_WORDS)
    if not theorem_explicitly_proved(summary):
        assert matching_items(summary, OPEN_THEOREM_WORDS)


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


def sprint108_modules(repo_root: Path = REPO_ROOT) -> list[Path]:
    return sorted((repo_root / "DASHI" / "Physics" / "Closure").glob(MODULE_GLOB))


def test_sprint108_fixture_summary_records_transfer_lower_bound_audit(
    tmp_path: Path,
) -> None:
    write_sprint108_module(
        tmp_path,
        "TransferLowerBoundAuditFixture",
        sprint108_fixture_module(),
    )

    summary = run_script(tmp_path, tmp_path / "out")

    assert_summary_records_transfer_lower_bound_audit(summary)


def test_sprint108_real_summary_records_transfer_lower_bound_audit(tmp_path: Path) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")

    assert_summary_records_transfer_lower_bound_audit(summary)


def test_sprint108_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sprint108_modules()
    if not module_paths:
        pytest.skip("Sprint108 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint108_modules_record_transfer_lower_bound_audit_surface() -> None:
    module_paths = sprint108_modules()
    if not module_paths:
        pytest.skip("Sprint108 Agda modules are not integrated yet")

    combined = "\n".join(path.read_text() for path in module_paths)
    assert TRANSFER_GAP_TARGET in combined or matching_items(combined, TARGET_WORDS)
    assert matching_items(combined, MODULE_MOSCO_NO_POLLUTION_WORDS)
    assert matching_items(combined, MODULE_LOG_GENERATOR_WORDS)
    assert matching_items(combined, MODULE_UNIFORM_FORM_LOWER_BOUND_WORDS)
    assert matching_items(combined, MODULE_SPECTRAL_TRANSPORT_WORDS)
    if not theorem_explicitly_proved(combined):
        assert matching_items(combined, OPEN_THEOREM_WORDS)
