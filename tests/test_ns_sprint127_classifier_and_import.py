from __future__ import annotations

import json
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "127"
EXPECTED_MODULE = (
    "DASHI.Physics.Closure."
    "NSSprint127AxisymmetricBoundaryVortexStretchingGate"
)
RECOMMENDED_NEXT_LEMMA = "BoundaryVorticityAmplificationLaw"


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


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


def sprint127_classifier() -> Path:
    classifiers = sorted(SCRIPT_DIR.glob("ns_sprint" + SPRINT + "*classifier.py"))
    assert len(classifiers) == 1, (
        "Sprint127 NS must expose exactly one classifier under scripts/; found: "
        + ", ".join(relative(path) for path in classifiers)
    )
    return classifiers[0]


def run_classifier(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], list[Any], str]:
    classifier = sprint127_classifier()
    out_dir = tmp_path / "ns_sprint127_classifier"
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


def values_for_keys_containing(payloads: list[Any], *terms: str) -> list[Any]:
    values: list[Any] = []
    folded_terms = tuple(term.lower() for term in terms)
    for item in json_values(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            key_text = str(key).lower()
            if all(term in key_text for term in folded_terms):
                values.append(value)
    return values


def assert_artifact_contains(output_text: str, *terms: str) -> None:
    folded_output = output_text.lower()
    for term in terms:
        assert term.lower() in folded_output, output_text


def test_sprint127_classifier_exits_1_and_recommends_boundary_law(
    tmp_path: Path,
) -> None:
    result, _payloads, output_text = run_classifier(tmp_path)

    assert result.returncode == 1, output_text
    assert RECOMMENDED_NEXT_LEMMA in output_text


def test_sprint127_classifier_records_required_route_classifications(
    tmp_path: Path,
) -> None:
    _result, payloads, output_text = run_classifier(tmp_path)

    assert dicts_with_terms(
        payloads,
        "axisymmetric",
        "boundary",
        "live_primary_open",
    ), output_text
    assert dicts_with_terms(
        payloads,
        "hou",
        "luo",
        "recorded_compatible",
    ), output_text
    assert dicts_with_terms(payloads, "clay", "not_promoted"), output_text
    assert_artifact_contains(
        output_text,
        "axisymmetric",
        "boundary",
        "live_primary_open",
        "hou",
        "luo",
        "recorded_compatible",
        "clay",
        "not_promoted",
    )
    assert True not in values_for_keys_containing(payloads, "clay")


def test_everything_imports_sprint127_after_integration() -> None:
    everything = EVERYTHING.read_text(encoding="utf-8", errors="replace")

    assert "import " + EXPECTED_MODULE in everything
