from __future__ import annotations

import csv
import json
import re
import shutil
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"
OUTPUTS_DIR = REPO_ROOT / "outputs"
SPRINT = 155
EXPECTED_SCRIPT_COUNT = 3
EXPECTED_LANES = {2, 3, 4}

SUMMARY_RE = re.compile(r"(?:^|_)summary(?:_|\.|$)", re.IGNORECASE)
TRUE_RE = re.compile(r"\btrue\b", re.IGNORECASE)

IDENTITY_PROOF_KEYWORDS = {
    "localized_identity_proved",
    "localized_identity_proof",
    "localized_identity_closed",
    "localized_enstrophy_identity_proved",
    "localized_enstrophy_identity_closed",
    "localized_identity_proof_closed",
    "localized_identity_proof_valid",
}

BKM_KEYWORDS = {
    "bkm",
    "symmetric_hou_luo_bkm_finite",
    "bkm_finite",
    "bkm_promoted",
    "bkm_closed",
    "bkm_guard_closed",
}
CLAY_KEYWORDS = {
    "clay",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "full_navier_stokes_theorem_proved",
    "navier_stokes_clay_promoted",
}
MODEL_KEYWORDS = {
    "model",
    "model_validity",
    "model_validity_closed",
    "model_validity_for_width_ode",
    "model_promoted",
    "model_closed",
}
PROMOTION_KEYWORDS = {
    "promotion",
    "promoted",
    "claim_closed",
    "claim_proved",
    "claim_proven",
    "theorem_proved",
}


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def normalize(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


def as_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.lower() in {"true", "false"}:
        return value.lower() == "true"
    return None


def discover_sprint155_scripts() -> list[Path]:
    return sorted(path for path in SCRIPT_DIR.glob("ns_sprint155_*.py") if path.is_file())


def script_supports_arg(script: Path, arg: str) -> bool:
    text = script.read_text(encoding="utf-8", errors="replace")
    return f'"{arg}"' in text or f"'{arg}'" in text


def output_dir_and_args(script: Path, scratch_dir: Path) -> tuple[Path, list[str]]:
    args: list[str] = []
    if script_supports_arg(script, "--repo-root"):
        args.extend(["--repo-root", str(REPO_ROOT)])
    if script_supports_arg(script, "--out-dir"):
        out_dir = scratch_dir / script.stem
        args.extend(["--out-dir", str(out_dir)])
        return out_dir, args
    return OUTPUTS_DIR / script.stem, args


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def artifact_text(paths: list[Path]) -> str:
    parts: list[str] = []
    for path in paths:
        if path.suffix.lower() in {".json", ".csv", ".md"}:
            parts.append(path.read_text(encoding="utf-8", errors="replace"))
    return "\n".join(parts)


def run_script(script: Path, scratch_dir: Path) -> tuple[list[Any], list[Any], list[Path], str, Path]:
    out_dir, args = output_dir_and_args(script, scratch_dir)
    result = subprocess.run(
        [sys.executable, str(script), *args],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    artifact_paths = sorted(path for path in out_dir.glob("*") if path.is_file()) if out_dir.exists() else []
    json_paths = [path for path in artifact_paths if path.suffix.lower() == ".json"]
    summary_paths = [path for path in json_paths if SUMMARY_RE.search(path.name)]
    text = "\n".join([result.stdout, result.stderr, artifact_text(artifact_paths)])

    assert result.returncode == 0, text
    assert out_dir.is_dir(), text
    assert artifact_paths, text
    assert summary_paths, [path.name for path in artifact_paths]

    assert any(path.name.endswith("_summary.json") for path in summary_paths), [
        path.name for path in summary_paths
    ]
    assert any(path.name.endswith("_rows.json") or path.name.endswith("_ledger.json") for path in json_paths), [
        path.name for path in json_paths
    ]
    assert any(path.name.endswith("_rows.csv") or path.name.endswith("_ledger.csv") for path in artifact_paths), [
        path.name for path in artifact_paths
    ]
    assert any(path.suffix.lower() == ".md" for path in artifact_paths), [path.name for path in artifact_paths]
    assert any(path.name.endswith("_manifest.json") for path in json_paths), [path.name for path in json_paths]
    assert all(path.stat().st_size > 0 for path in artifact_paths)
    assert all(script.stem in path.name for path in artifact_paths), [path.name for path in artifact_paths]

    payloads = [load_json(path) for path in json_paths]
    summaries = [load_json(path) for path in summary_paths]
    return summaries, payloads, artifact_paths, text, out_dir


def lane_values(values: list[Any]) -> set[int]:
    lanes: set[int] = set()
    for item in walk(values):
        if not isinstance(item, dict) or "lane" not in item:
            continue
        value = item["lane"]
        if isinstance(value, int) and not isinstance(value, bool):
            lanes.add(value)
        elif isinstance(value, str) and value.isdigit():
            lanes.add(int(value))
    return lanes


def bool_items(values: list[Any]) -> Iterable[tuple[str, bool]]:
    for item in walk(values):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            parsed = as_bool(value)
            if parsed is not None:
                yield normalize(key), parsed


def rows_from_artifacts(payloads: list[Any], artifact_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in walk(payloads):
        if isinstance(item, dict) and any(normalize(key) in {"row_id", "status", "classification"} for key in item):
            rows.append(item)
    for path in artifact_paths:
        if path.suffix.lower() != ".csv":
            continue
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def key_matches(key: str, keywords: set[str]) -> bool:
    return any(keyword in key for keyword in keywords)


def is_intentional_model_assembler(script: Path, summaries: list[Any], text: str) -> bool:
    haystack = normalize(
        " ".join(
            [
                script.stem,
                text,
                json.dumps(summaries, sort_keys=True, default=str),
            ]
        )
    )
    return ("assembler" in haystack or "assembly" in haystack) and (
        "model_only" in haystack or "model_closed" in haystack or "closes_model" in haystack
    )


def is_false_certificate_key(key: str) -> bool:
    return (
        key.endswith("_false")
        or key.endswith("_is_false")
        or "_is_false" in key
        or key.startswith("all_") and key.endswith("_false")
    )


def is_active_guard_key(key: str) -> bool:
    return "guard" in key and not any(
        marker in key
        for marker in (
            "closed",
            "promoted",
            "promotion",
            "can_promote",
            "solved",
            "finite",
            "proved",
            "proven",
        )
    )


def assert_identity_proof_flags(summaries: list[Any], script: Path, text: str) -> bool:
    identity_flags = [
        value
        for key, value in bool_items(summaries)
        if key in IDENTITY_PROOF_KEYWORDS
        or (
            "localized" in key
            and "identity" in key
            and ("proof" in key or "proved" in key or "closed" in key)
        )
    ]
    if not identity_flags:
        assert "identity" not in normalize(script.stem), f"identity script has no summary proof flag\n{text}"
        return False
    assert all(identity_flags), (script.name, identity_flags)
    return True


def assert_downstream_promotions_fail_closed(
    summaries: list[Any],
    payloads: list[Any],
    script: Path,
    text: str,
) -> None:
    values = list(bool_items([summaries, payloads]))
    assembler_model_only = is_intentional_model_assembler(script, summaries, text)
    guard_values = 0

    for key, value in values:
        is_bkm = key_matches(key, BKM_KEYWORDS)
        is_clay = key_matches(key, CLAY_KEYWORDS)
        is_model = key_matches(key, MODEL_KEYWORDS)
        is_promotion = key_matches(key, PROMOTION_KEYWORDS)

        if is_bkm or is_clay:
            if is_false_certificate_key(key):
                assert value is True, (script.name, key, value)
                guard_values += 1
                continue
            if is_active_guard_key(key):
                assert value is True, (script.name, key, value)
                guard_values += 1
                continue
            assert value is False, (script.name, key, value)
            guard_values += 1
            continue

        if is_model and (is_promotion or "closed" in key or "validity" in key):
            if is_false_certificate_key(key):
                assert value is True, (script.name, key, value)
                guard_values += 1
                continue
            if assembler_model_only and not is_bkm and not is_clay:
                guard_values += 1
                continue
            assert value is False, (script.name, key, value)
            guard_values += 1
            continue

        if is_promotion and not ("localized" in key and "identity" in key):
            assert value is False, (script.name, key, value)
            guard_values += 1

    assert guard_values, f"missing model/BKM/Clay promotion guard flags\n{text}"
    forbidden_true_patterns = (
        r'"[^"]*(?:promotion|promoted|can_promote|solution|solved)[^"]*"\s*:\s*true\b',
    )
    for pattern in forbidden_true_patterns:
        assert not re.search(pattern, text, flags=re.IGNORECASE), pattern
    if not assembler_model_only:
        assert not re.search(r'"[^"]*model[^"]*"\s*:\s*true\b', text, flags=re.IGNORECASE), script.name


def test_sprint155_expected_worker_emitters_are_present() -> None:
    scripts = discover_sprint155_scripts()
    assert len(scripts) == EXPECTED_SCRIPT_COUNT, [path.name for path in scripts]


def test_sprint155_emitters_write_required_outputs_and_fail_closed_summaries(tmp_path: Path) -> None:
    scripts = discover_sprint155_scripts()
    assert scripts, "missing all Sprint155 emitter scripts"

    scratch_dir = OUTPUTS_DIR / ".pytest_ns_sprint155_emitters" / tmp_path.name
    if scratch_dir.exists():
        shutil.rmtree(scratch_dir)
    scratch_dir.mkdir(parents=True)

    observed_lanes: set[int] = set()
    observed_identity_proof = False
    try:
        for script in scripts:
            summaries, payloads, artifact_paths, text, out_dir = run_script(script, scratch_dir)
            rows = rows_from_artifacts(payloads, artifact_paths)

            assert out_dir.name == script.stem
            assert f"ns_sprint{SPRINT}" in script.stem
            assert rows, text
            assert any(
                item.get("sprint") in {SPRINT, str(SPRINT)}
                for item in walk([summaries, payloads, rows])
                if isinstance(item, dict)
            ), text

            lanes = lane_values([summaries, payloads, rows])
            assert len(lanes) == 1, lanes
            lane = next(iter(lanes))
            assert lane in EXPECTED_LANES
            observed_lanes.add(lane)

            observed_identity_proof |= assert_identity_proof_flags(summaries, script, text)
            assert_downstream_promotions_fail_closed(summaries, payloads, script, text)
    finally:
        shutil.rmtree(scratch_dir, ignore_errors=True)

    assert observed_lanes == EXPECTED_LANES
    assert len(scripts) == EXPECTED_SCRIPT_COUNT, [path.name for path in scripts]
    assert observed_identity_proof, "no Sprint155 summary asserted a localized identity proof"
