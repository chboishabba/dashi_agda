from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint138_global_concavity_blocker"
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
    "blocker",
    "gap",
    "not_closed",
    "unresolved",
    "fail_closed",
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


def run_blocker(tmp_path: Path) -> tuple[dict[str, Any], str, list[Path], list[Path]]:
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
            if path.suffix.lower() in {".json", ".md", ".txt", ".csv"}
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
    md_paths = [path for path in artifact_paths if path.suffix.lower() == ".md"]
    assert json_paths, artifact_text
    assert md_paths, artifact_text
    assert all(path.stat().st_size > 0 for path in json_paths + md_paths), artifact_text

    summary = load_summary(out_dir, json_paths)
    return summary, artifact_text, json_paths, md_paths


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
        for key in (
            "status",
            "state",
            "classification",
            "closure_status",
            "proof_status",
            "blocker_status",
            "gate_status",
        ):
            if key in item:
                statuses.append(item[key])
    return compact_json(statuses)


def assert_all_false(summary: dict[str, Any], *keys: str) -> None:
    values = bool_values_for_keys(summary, *keys)
    assert values, f"missing boolean values for {keys}: {json.dumps(summary, indent=2, sort_keys=True)}"
    assert all(value is False for value in values), json.dumps(values)


def assert_any_false(summary: dict[str, Any], *keys: str) -> None:
    values = bool_values_for_keys(summary, *keys)
    assert values, f"missing boolean value for one of {keys}: {json.dumps(summary, indent=2, sort_keys=True)}"
    assert all(value is False for value in values), json.dumps(values)


def test_sprint138_global_concavity_blocker_records_fail_closed_outputs(
    tmp_path: Path,
) -> None:
    summary, artifact_text, json_paths, md_paths = run_blocker(tmp_path)
    artifact_compact = compact_json(artifact_text)

    assert json_paths, artifact_text
    assert md_paths, artifact_text

    local_concavity_flags = bool_values_for_keys(
        summary,
        "local_concavity_supported",
        "local_concavity_support",
        "local_barrier_supported",
        "local_barrier_support",
    )
    assert local_concavity_flags and all(local_concavity_flags), json.dumps(
        summary, indent=2, sort_keys=True
    )

    assert_any_false(
        summary,
        "global_concavity_closed",
        "global_closure_closed",
        "global_proof_closed",
    )
    assert_any_false(
        summary,
        "global_concavity_proved",
        "global_concavity_proven",
        "global_proof_proved",
        "global_proof_proven",
    )

    blocker_status = status_text_for(summary, "global_concavity")
    blocker_values = values_for_key_fragments(summary, "blocker", "obstruction", "gap")
    blocker_text = compact_json(blocker_values + [blocker_status])
    assert any(term in blocker_text for term in OPEN_TERMS), blocker_text
    assert not any(
        re.search(rf"(?:^|_){term}(?:_|$)", blocker_status) for term in CLOSED_TERMS
    ), blocker_status

    for term in (
        "kernel",
        "sign_indefinite",
        "nonlocal",
        "boundary_persistence",
    ):
        assert term in artifact_compact, term

    assert_all_false(summary, "full_clay_ns_solved", "full_clay_solved")
    assert_all_false(
        summary,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
    )
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(artifact_text), pattern.pattern
