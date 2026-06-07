from __future__ import annotations

import json
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPT_DIR = REPO_ROOT / "scripts"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "124"
EXPECTED_STEM = "NSSprint124ZeroMeanFluxOverRotationCycle"
EXPECTED_MODULE = "DASHI.Physics.Closure." + EXPECTED_STEM
EXPECTED_FILE = AGDA_DIR / (EXPECTED_STEM + ".agda")
EXPECTED_PREVIOUS_MODULE = (
    "DASHI.Physics.Closure.NSSprint123RotatingFramePhaseLockingEstimate"
)

RECOMMENDED_NEXT_LEMMA = "VortexStretchingAmplificationVsDepletionBound"
PROMOTION_FLAG = "clay" + "Navier" + "Stokes" + "Promoted"

TOKEN_TRUE = "tr" + "ue"
TOKEN_FALSE = "fa" + "lse"


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def sprint124_classifier() -> Path:
    classifiers = sorted(SCRIPT_DIR.glob("ns_sprint" + SPRINT + "*classifier.py"))
    assert classifiers == [SCRIPT_DIR / "ns_sprint124_route_classifier.py"], (
        "Sprint124 NS must expose exactly one route classifier at "
        "scripts/ns_sprint124_route_classifier.py; found: "
        + ", ".join(relative(path) for path in classifiers)
    )
    return classifiers[0]


def sprint124_ns_agda_module() -> Path:
    modules = sorted(path for path in AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda") if path.is_file())
    assert modules == [EXPECTED_FILE], (
        "Sprint124 NS must have exactly one Agda file, "
        + relative(EXPECTED_FILE)
        + "; found: "
        + ", ".join(relative(path) for path in modules)
    )
    assert agda_module_name(EXPECTED_FILE) == EXPECTED_MODULE
    return EXPECTED_FILE


def json_values(payload: Any) -> Iterable[Any]:
    if isinstance(payload, dict):
        yield payload
        for value in payload.values():
            yield from json_values(value)
    elif isinstance(payload, list):
        for value in payload:
            yield from json_values(value)
    else:
        yield payload


def payload_text(payloads: list[Any]) -> str:
    return json.dumps(payloads, sort_keys=True)


def bool_values_for_terms(payloads: list[Any], *terms: str) -> list[bool]:
    values: list[bool] = []
    folded_terms = tuple(term.lower() for term in terms)
    for item in json_values(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            key_text = str(key).lower()
            value_text = str(value).lower()
            if all(term in key_text or term in value_text for term in folded_terms):
                if isinstance(value, bool):
                    values.append(value)
    return values


def dicts_with_terms(payloads: list[Any], *terms: str) -> list[dict[str, Any]]:
    matches: list[dict[str, Any]] = []
    folded_terms = tuple(term.lower() for term in terms)
    for item in json_values(payloads):
        if not isinstance(item, dict):
            continue
        item_text = json.dumps(item, sort_keys=True).lower()
        if all(term in item_text for term in folded_terms):
            matches.append(item)
    return matches


def run_classifier(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], list[Any], str]:
    classifier = sprint124_classifier()
    out_dir = tmp_path / "ns_sprint124_route_classifier"
    result = subprocess.run(
        [sys.executable, str(classifier), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    json_files = sorted(out_dir.glob("*.json"))
    markdown_files = sorted(out_dir.glob("*.md"))
    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_files]
    artifact_text = "\n".join(
        path.read_text(encoding="utf-8", errors="replace")
        for path in json_files + markdown_files
        if path.is_file()
    )
    output_text = "\n".join((result.stdout, result.stderr, artifact_text))

    assert json_files, output_text
    assert markdown_files, output_text
    return result, payloads, output_text


def bool_assignment_pattern(identifier: str, value: bool) -> re.Pattern[str]:
    agda_value = TOKEN_TRUE if value else TOKEN_FALSE
    return re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(identifier)
        + r"(?![A-Za-z0-9_])"
        + r"(?:\s*:\s*[^\n=]+)?\s*=\s*"
        + agda_value
        + r"(?![A-Za-z0-9_])",
        re.MULTILINE,
    )


def test_sprint124_classifier_exits_1_and_recommends_vortex_bound(
    tmp_path: Path,
) -> None:
    result, payloads, output_text = run_classifier(tmp_path)
    text = payload_text(payloads)

    assert result.returncode == 1, output_text
    assert RECOMMENDED_NEXT_LEMMA in output_text
    assert re.search(
        r'"recommended_next_lemma"\s*:\s*"'
        + re.escape(RECOMMENDED_NEXT_LEMMA)
        + r'"',
        text,
    ), output_text


def test_sprint124_classifier_keeps_rotating_route_obstructed_and_clay_false(
    tmp_path: Path,
) -> None:
    _result, payloads, output_text = run_classifier(tmp_path)
    folded_output = output_text.lower()

    assert re.search(r"rotating[^.\n]*(obstruct|blocked|fail[-_ ]closed)", folded_output)
    assert re.search(r"vortex[^.\n]*(stretching|amplification)", folded_output)

    rotating_rows = dicts_with_terms(payloads, "rotating_strain_flux_budget", "obstruct")
    assert rotating_rows, output_text

    clay_values = bool_values_for_terms(payloads, "clay")
    assert clay_values and not any(clay_values), output_text
    assert re.search(r"clay[^.\n]*(false|not[-_ ]promoted|no promotion)", folded_output)
    assert not re.search(r"clay[A-Za-z0-9_]*\s*[:=]\s*" + TOKEN_TRUE, output_text)


def test_everything_imports_sprint124_and_agda_surface_has_key_anchors() -> None:
    path = sprint124_ns_agda_module()
    everything = read_text(EVERYTHING)
    text = read_text(path)
    compact_text = re.sub(r"\s+", "", text)

    assert "import " + EXPECTED_MODULE in everything
    assert "module " + EXPECTED_MODULE + " where" in text
    assert "import " + EXPECTED_PREVIOUS_MODULE in text
    assert "ZeroMeanFluxOverRotationCycle" in text
    assert "VortexStretchingNextRoute" in text
    assert "VortexStretchingContinuumControl" in text
    assert "RotatingFramePhaseLockingEstimate" in text
    assert "obstruction" in text.lower()
    assert bool_assignment_pattern("rotatingStrainRouteClosed", True).search(text)
    assert bool_assignment_pattern(PROMOTION_FLAG, False).search(text)
    assert (PROMOTION_FLAG + "=" + TOKEN_FALSE) in compact_text
