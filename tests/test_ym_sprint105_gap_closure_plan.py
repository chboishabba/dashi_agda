from __future__ import annotations

import json
import re
import subprocess
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint105_gap_closure_plan.py"
SUMMARY_NAME = "ym_sprint105_gap_closure_plan_summary.json"
MODULE_GLOB = "YMSprint105*.agda"

FORBIDDEN_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
)
FORBIDDEN_PROMOTION = "clayYangMillsPromoted = " + "true"

OBLIGATION_PHRASES = {
    "transfer-gap lower bound": ("transfer", "gap", "lower", "bound"),
    "symmetry restoration": ("symmetry", "restoration"),
    "compact simple group parameter table/completeness audit": (
        "compact",
        "simple",
        "group",
        "table",
    ),
}

REDUCTION_PHRASES = {
    "WC3-only m_eff positivity": ("wc3", "m", "eff", "positive"),
    "asymptotic-freedom scale boundary": ("asymptotic", "freedom", "scale"),
    "OS3/spatial-only blocking": ("os3", "spatial", "blocking"),
    "symmetry restoration": ("symmetry", "restoration"),
    "compact simple group table": ("compact", "simple", "group", "table"),
}


def run_script(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    if not SCRIPT.exists():
        pytest.skip("Sprint105 gap closure plan script is not integrated yet")

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


def write_sprint105_module(repo_root: Path, name: str, text: str) -> None:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    (module_dir / f"YMSprint105{name}.agda").write_text(text)


def sprint105_fixture_module() -> str:
    return textwrap.dedent(
        """\
        module DASHI.Physics.Closure.YMSprint105GapClosurePlan where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        transferGapLowerBoundObligation : String
        transferGapLowerBoundObligation =
          "transfer-gap lower bound"

        symmetryRestorationObligation : String
        symmetryRestorationObligation =
          "symmetry restoration"

        compactSimpleGroupParameterTableCompletenessAudit : String
        compactSimpleGroupParameterTableCompletenessAudit =
          "compact simple group parameter table completeness audit"

        wc3OnlyEffectiveMassPositivity : String
        wc3OnlyEffectiveMassPositivity =
          "WC3 only m eff positive"

        asymptoticFreedomScaleBoundary : String
        asymptoticFreedomScaleBoundary =
          "asymptotic freedom scale boundary"

        os3SpatialOnlyBlocking : String
        os3SpatialOnlyBlocking =
          "OS3 spatial only blocking"
        """
    )


def normalized_words(value: Any) -> set[str]:
    words = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(words):
        if word.startswith("positiv"):
            words.add("positive")
        if word.startswith("block"):
            words.add("blocking")
        if word.startswith("restor"):
            words.add("restoration")
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


def top_level_obligation_items(summary: dict[str, Any]) -> list[Any]:
    candidates: list[Any] = []
    for key, value in summary.items():
        words = normalized_words(key)
        if "obligation" in words or {"gap", "closure"}.issubset(words):
            if isinstance(value, list):
                candidates.extend(value)
            elif isinstance(value, dict):
                candidates.extend(value.values())
            else:
                candidates.append(value)
    return candidates or flatten_values(summary)


def has_empty_data_declaration(text: str) -> bool:
    lines = text.splitlines()
    for index, line in enumerate(lines):
        if not re.match(r"^data\s+\S+.*\bwhere\s*$", line):
            continue

        saw_constructor = False
        for following in lines[index + 1 :]:
            if not following.strip() or following.lstrip().startswith("--"):
                continue
            if not following.startswith((" ", "\t")):
                break
            saw_constructor = True
            break
        if not saw_constructor:
            return True
    return False


def test_sprint105_fixture_summary_records_three_remaining_native_obligations(
    tmp_path: Path,
) -> None:
    write_sprint105_module(tmp_path, "GapClosurePlan", sprint105_fixture_module())

    summary = run_script(tmp_path, tmp_path / "out")
    obligation_items = top_level_obligation_items(summary)

    for label, phrase in OBLIGATION_PHRASES.items():
        assert matching_items(obligation_items, phrase), label

    count_values = [
        value
        for key, value in summary.items()
        if "obligation" in normalized_words(key)
        and "count" in normalized_words(key)
        and isinstance(value, int)
    ]
    if count_values:
        assert 3 in count_values


def test_sprint105_real_summary_includes_obligations_and_reductions(
    tmp_path: Path,
) -> None:
    summary = run_script(REPO_ROOT, tmp_path / "out")
    obligation_items = top_level_obligation_items(summary)

    for label, phrase in OBLIGATION_PHRASES.items():
        assert matching_items(obligation_items, phrase), label

    for label, phrase in REDUCTION_PHRASES.items():
        assert matching_items(summary, phrase), label

    if "remaining_obligation_count" in summary:
        assert summary["remaining_obligation_count"] == 3
    elif "remaining_theorem_obligation_count" in summary:
        assert summary["remaining_theorem_obligation_count"] == 3


def test_sprint105_modules_have_no_placeholders_empty_data_or_promotion() -> None:
    module_paths = sorted(
        (REPO_ROOT / "DASHI" / "Physics" / "Closure").glob(MODULE_GLOB)
    )
    if not module_paths:
        pytest.skip("Sprint105 Agda modules are not integrated yet")

    for module_path in module_paths:
        text = module_path.read_text()
        for token in FORBIDDEN_TOKENS:
            assert token not in text, module_path
        assert FORBIDDEN_PROMOTION not in text, module_path
        assert not has_empty_data_declaration(text), module_path


def test_sprint105_modules_represent_required_reductions() -> None:
    module_paths = sorted(
        (REPO_ROOT / "DASHI" / "Physics" / "Closure").glob(MODULE_GLOB)
    )
    if not module_paths:
        pytest.skip("Sprint105 Agda modules are not integrated yet")

    text = "\n".join(path.read_text() for path in module_paths)
    words = normalized_words(text)

    for label, phrase in REDUCTION_PHRASES.items():
        assert all(word in words for word in phrase), label
