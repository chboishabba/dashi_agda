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
SPRINT = 156
EXPECTED_SCRIPT_COUNT = 3
EXPECTED_LANES = {2, 3, 4}

SUMMARY_RE = re.compile(r"(?:^|_)summary(?:_|\.|$)", re.IGNORECASE)

MODEL_TRUE_KEYS = {
    "model_validity",
    "model_validity_closed",
    "model_validity_for_width_ode",
    "model_validity_for_width_ode_proved",
    "modelvalidityforwidthode",
    "modelvalidityforwidthodeproved",
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
PROMOTION_KEYWORDS = {
    "promotion",
    "promoted",
    "can_promote",
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


def compact_key(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "", str(value).lower())


def as_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.lower() in {"true", "false"}:
        return value.lower() == "true"
    return None


def discover_sprint156_scripts() -> list[Path]:
    return sorted(path for path in SCRIPT_DIR.glob("ns_sprint156_*.py") if path.is_file())


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
    if script_supports_arg(script, "--output-dir"):
        out_dir = scratch_dir / script.stem
        args.extend(["--output-dir", str(out_dir)])
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


def is_false_certificate_key(key: str) -> bool:
    return (
        key.endswith("_false")
        or key.endswith("_is_false")
        or "_is_false" in key
        or key.startswith("all_") and key.endswith("_false")
        or key.startswith("no_")
        or key.endswith("_fail_closed")
        or "fail_closed" in key
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


def is_downstream_claim_key(key: str) -> bool:
    if key_matches(key, BKM_KEYWORDS):
        return any(
            marker in key
            for marker in (
                "finite",
                "promoted",
                "promotion",
                "can_promote",
                "integral_estimate",
                "claim",
                "theorem",
                "proved",
                "proven",
                "closed",
                "solved",
            )
        )
    if key_matches(key, CLAY_KEYWORDS):
        return any(
            marker in key
            for marker in (
                "full_clay",
                "clay_navier",
                "solved",
                "promoted",
                "promotion",
                "can_promote",
                "mechanism_exhausted",
                "claim",
                "theorem",
                "proved",
                "proven",
            )
        )
    return False


def is_model_validity_key(key: str) -> bool:
    return key in MODEL_TRUE_KEYS or compact_key(key) in MODEL_TRUE_KEYS


def dict_context(value: dict[str, Any]) -> str:
    return normalize(
        " ".join(
            str(value.get(key, ""))
            for key in ("row_id", "normalized_name", "category", "status", "expression")
        )
    )


def model_validity_bool_items(values: list[Any]) -> Iterable[tuple[str, bool, str]]:
    for item in walk(values):
        if not isinstance(item, dict):
            continue
        context = dict_context(item)
        for key, value in item.items():
            parsed = as_bool(value)
            if parsed is not None and is_model_validity_key(normalize(key)):
                yield normalize(key), parsed, context


def assert_model_validity_true_where_present(
    summaries: list[Any],
    payloads: list[Any],
    script: Path,
    text: str,
) -> bool:
    summary_model_values = [
        value
        for key, value, _ in model_validity_bool_items(summaries)
    ]
    model_items = list(model_validity_bool_items([summaries, payloads]))
    if not model_items:
        assert "model" not in normalize(script.stem), f"model-validity script has no model-validity bool\n{text}"
        return False

    assert all(summary_model_values), (script.name, summary_model_values)
    true_model_items = [(key, context) for key, value, context in model_items if value]
    assert true_model_items, (script.name, model_items)

    inappropriate_false_items = [
        (key, context)
        for key, value, context in model_items
        if value is False
        and ("model_validity_for_width_ode" in context or "modelvalidityforwidthode" in compact_key(context))
    ]
    assert not inappropriate_false_items, (script.name, inappropriate_false_items)
    return bool(summary_model_values or true_model_items)


def assert_bkm_clay_and_promotion_fail_closed(
    summaries: list[Any],
    payloads: list[Any],
    script: Path,
    text: str,
) -> None:
    guard_values = 0
    for key, value in bool_items([summaries, payloads]):
        if is_model_validity_key(key):
            continue

        is_bkm = key_matches(key, BKM_KEYWORDS)
        is_clay = key_matches(key, CLAY_KEYWORDS)
        is_promotion = key_matches(key, PROMOTION_KEYWORDS)

        if is_bkm or is_clay:
            if is_false_certificate_key(key) or is_active_guard_key(key):
                assert value is True, (script.name, key, value)
                guard_values += 1
                continue
            if not is_downstream_claim_key(key):
                continue
            assert value is False, (script.name, key, value)
            guard_values += 1
            continue

        if is_promotion:
            if is_false_certificate_key(key):
                assert value is True, (script.name, key, value)
                guard_values += 1
                continue
            if "input" in key or "readiness" in key or "support" in key:
                continue
            assert value is False, (script.name, key, value)
            guard_values += 1

    assert guard_values, f"missing BKM/Clay/promotion guard flags\n{text}"
    forbidden_true_patterns = (
        r'"(?:bkm_finite|symmetric_hou_luo_bkm_finite|bkm_promoted|bkm_guard_closed|'
        r'full_clay_ns_solved|full_clay_can_promote|clay_navier_stokes_promoted|'
        r'promotion_allowed|clay_promotion_allowed)"\s*:\s*true\b',
    )
    for pattern in forbidden_true_patterns:
        assert not re.search(pattern, text, flags=re.IGNORECASE), (script.name, pattern)


def test_sprint156_expected_worker_emitters_are_present() -> None:
    scripts = discover_sprint156_scripts()
    assert len(scripts) == EXPECTED_SCRIPT_COUNT, [path.name for path in scripts]


def test_sprint156_emitters_write_required_outputs_and_guard_promotions(tmp_path: Path) -> None:
    scripts = discover_sprint156_scripts()
    assert scripts, "missing all Sprint156 emitter scripts"

    scratch_dir = OUTPUTS_DIR / ".pytest_ns_sprint156_emitters" / tmp_path.name
    if scratch_dir.exists():
        shutil.rmtree(scratch_dir)
    scratch_dir.mkdir(parents=True)

    observed_lanes: set[int] = set()
    observed_model_validity = False
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

            observed_model_validity |= assert_model_validity_true_where_present(
                summaries,
                payloads,
                script,
                text,
            )
            assert_bkm_clay_and_promotion_fail_closed(summaries, payloads, script, text)
    finally:
        shutil.rmtree(scratch_dir, ignore_errors=True)

    assert observed_lanes == EXPECTED_LANES
    assert len(scripts) == EXPECTED_SCRIPT_COUNT, [path.name for path in scripts]
    assert observed_model_validity, "no Sprint156 artifact asserted ModelValidityForWidthODE/model_validity true"
