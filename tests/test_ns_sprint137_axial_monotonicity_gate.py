from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint137_axial_monotonicity_gate"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
SUMMARY_NAME = f"{STEM}_summary.json"

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)

OPEN_TERMS = {
    "open",
    "blocked",
    "gap",
    "not_closed",
    "unresolved",
    "open_live_candidate",
}
CLOSED_TERMS = {
    "closed",
    "proved",
    "proven",
    "complete",
    "resolved",
    "unconditional",
    "promoted",
}


def run_gate(tmp_path: Path) -> tuple[dict[str, Any], str, list[Path]]:
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

    artifact_paths = sorted(
        path
        for path in out_dir.glob("*")
        if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
    ) if out_dir.exists() else []
    artifact_text = "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in artifact_paths]
    )

    assert result.returncode == 0, artifact_text
    assert out_dir.is_dir(), artifact_text
    json_paths = [path for path in artifact_paths if path.suffix.lower() == ".json"]
    md_paths = [path for path in artifact_paths if path.suffix.lower() == ".md"]
    assert json_paths, artifact_text
    assert md_paths, artifact_text
    assert all(path.stat().st_size > 0 for path in json_paths + md_paths), artifact_text

    summary = load_summary(out_dir, json_paths)
    return summary, artifact_text, md_paths


def load_summary(out_dir: Path, json_paths: list[Path]) -> dict[str, Any]:
    preferred = out_dir / SUMMARY_NAME
    if preferred in json_paths:
        payload = json.loads(preferred.read_text(encoding="utf-8"))
        assert isinstance(payload, dict) and payload, f"{preferred.name} must be a nonempty object"
        return payload

    merged: dict[str, Any] = {}
    for path in json_paths:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(payload, dict):
            merged.update(payload)
    assert merged, "expected a nonempty JSON summary object"
    return merged


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def norm(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


def compact_json(value: Any) -> str:
    return norm(json.dumps(value, sort_keys=True, default=str))


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


def values_for_key_fragments(payload: Any, *fragments: str) -> list[Any]:
    wanted = tuple(fragment.lower() for fragment in fragments)
    found: list[Any] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if any(fragment in str(key).lower() for fragment in wanted):
                found.append(value)
    return found


def status_text_for(summary: dict[str, Any], identity: str) -> str:
    wanted = norm(identity)
    statuses: list[Any] = []
    for item in walk(summary):
        if not isinstance(item, dict):
            continue
        if wanted not in compact_json(item):
            continue
        for key in ("status", "state", "classification", "closure_status", "gate_status"):
            if key in item:
                statuses.append(item[key])
    return compact_json(statuses)


def test_sprint137_axial_monotonicity_gate_records_open_summary_and_report(
    tmp_path: Path,
) -> None:
    summary, artifact_text, md_paths = run_gate(tmp_path)
    summary_text = compact_json(summary)

    assert md_paths, artifact_text
    assert any(path.stat().st_size > 0 for path in md_paths), artifact_text

    axial_status = status_text_for(summary, "AxialMonotonicityOfSwirlProfile")
    assert axial_status, json.dumps(summary, indent=2, sort_keys=True, default=str)
    assert any(term in axial_status for term in OPEN_TERMS), axial_status
    assert not any(term in axial_status for term in CLOSED_TERMS), axial_status

    local_barrier_flags = bool_values_for_keys(
        summary,
        "local_barrier_supported",
        "local_barrier_support",
        "axial_monotonicity_local_barrier_supported",
    )
    assert local_barrier_flags and all(local_barrier_flags), json.dumps(summary, indent=2)

    global_proof_flags = bool_values_for_keys(
        summary,
        "global_proof_closed",
        "global_axisymmetric_proof_closed",
        "axial_monotonicity_global_proof_closed",
    )
    assert global_proof_flags and not any(global_proof_flags), json.dumps(summary, indent=2)

    blocker_values = values_for_key_fragments(summary, "blocker", "gap", "obstruction")
    blocker_text = compact_json(blocker_values + [summary])
    assert "secondary_peak" in blocker_text, blocker_text
    assert "global_concavity" in blocker_text, blocker_text

    full_clay_flags = bool_values_for_keys(summary, "full_clay_ns_solved", "full_clay_solved")
    promotion_flags = bool_values_for_keys(
        summary,
        "clayNavierStokesPromoted",
        "clay_navier_stokes_promoted",
        "clay_promoted",
    )
    assert full_clay_flags and all(value is False for value in full_clay_flags), summary_text
    assert promotion_flags and all(value is False for value in promotion_flags), summary_text
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(artifact_text), pattern.pattern
