from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint139_commutator_sign_route"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
SPRINT139_MODULE = "DASHI.Physics.Closure.NSSprint139AxialBarrierRouteForkReceipt"

CLAY_TRUE_PATTERNS = (
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bpromotion[_\s-]*decision\b\s*[:=]\s*(?:promote|promoted)\b", re.IGNORECASE),
)


def run_commutator_route(tmp_path: Path) -> tuple[list[Any], str, Path]:
    assert SCRIPT.is_file(), "missing " + str(SCRIPT.relative_to(REPO_ROOT))

    out_dir = tmp_path / STEM
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    artifact_paths = (
        sorted(
            path
            for path in out_dir.glob("*")
            if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
        )
        if out_dir.exists()
        else []
    )
    artifact_text = "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in artifact_paths]
    )

    assert result.returncode == 0, artifact_text
    assert out_dir.is_dir(), artifact_text

    json_paths = [path for path in artifact_paths if path.suffix.lower() == ".json"]
    csv_paths = [path for path in artifact_paths if path.suffix.lower() == ".csv"]
    md_paths = [path for path in artifact_paths if path.suffix.lower() == ".md"]
    assert json_paths, artifact_text
    assert csv_paths, artifact_text
    assert md_paths, artifact_text
    assert all(path.stat().st_size > 0 for path in json_paths + csv_paths + md_paths)

    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    assert payloads, artifact_text
    return payloads, artifact_text, out_dir


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def normalize(value: Any) -> str:
    text = str(value)
    replacements = {
        "Γ": "gamma",
        "γ": "gamma",
        "∂": "partial",
        "ᵣ": "r",
        "ᶻ": "z",
        "¹": "1",
        "²": "2",
        "^": " ",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return re.sub(r"[^a-z0-9]+", " ", text.lower()).strip()


def compact(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", normalize(value)).strip("_")


def joined_text(*values: Any) -> str:
    return "\n".join(
        value if isinstance(value, str) else json.dumps(value, sort_keys=True, default=str)
        for value in values
    )


def bool_values_for_keys(payload: Any, *keys: str) -> list[bool]:
    wanted = {key.lower() for key in keys}
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if str(key).lower() in wanted and isinstance(value, bool):
                values.append(value)
    return values


def rows_mentioning(payload: Any, *terms: str) -> list[dict[str, Any]]:
    wanted = tuple(normalize(term) for term in terms)
    rows: list[dict[str, Any]] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        text = normalize(json.dumps(item, sort_keys=True, default=str))
        if all(term in text for term in wanted):
            rows.append(item)
    return rows


def assert_text_has_all(text: str, *terms: str) -> None:
    haystack = normalize(text)
    missing = [term for term in terms if normalize(term) not in haystack]
    assert not missing, f"missing terms {missing} in:\n{text}"


def assert_all_false(payloads: list[Any], text: str, *keys: str) -> None:
    values = bool_values_for_keys(payloads, *keys)
    assert values, f"missing boolean values for {keys}:\n{text}"
    assert all(value is False for value in values), json.dumps(values)


def assert_no_clay_solution_or_promotion(payloads: list[Any], text: str) -> None:
    assert_all_false(payloads, text, "full_clay_ns_solved", "full_clay_solved")
    assert_all_false(
        payloads,
        text,
        "clayNavierStokesPromoted",
        "clay_navier_stokes_promoted",
        "clay_promoted",
    )
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_sprint139_commutator_route_emits_fail_closed_artifacts(tmp_path: Path) -> None:
    payloads, text, out_dir = run_commutator_route(tmp_path)
    combined = joined_text(payloads, text)

    assert out_dir.name == STEM
    assert_text_has_all(
        combined,
        "commutator",
        "domination",
        "sign",
        "route",
        "axial",
        "barrier",
    )
    assert rows_mentioning(payloads, "commutator", "domination"), combined
    assert rows_mentioning(payloads, "global", "barrier"), combined

    assert_all_false(payloads, text, "commutator_domination_closed")
    assert_all_false(payloads, text, "commutator_domination_proved")
    assert_all_false(payloads, text, "commutator_domination_proven")
    assert_all_false(payloads, text, "global_barrier_closed")
    assert_no_clay_solution_or_promotion(payloads, text)


def test_sprint139_agda_receipt_is_imported_by_everything() -> None:
    assert EVERYTHING.is_file(), "missing " + str(EVERYTHING.relative_to(REPO_ROOT))
    source = EVERYTHING.read_text(encoding="utf-8")

    pattern = re.compile(rf"^\s*import\s+{re.escape(SPRINT139_MODULE)}\s*$", re.MULTILINE)
    assert pattern.search(source), (
        "DASHI/Everything.agda must import " + SPRINT139_MODULE
    )
