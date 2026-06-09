from __future__ import annotations

import ast
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
SPRINT = 153
EXPECTED_LANES = {2, 3, 4}
CONTROL_CARD_KEYS = {"O", "R", "C", "S", "L", "P", "G", "F"}

FALSE_GUARD_NAMES = {
    "bkm_finite",
    "claim_closed",
    "claim_proved",
    "claim_proven",
    "full_theorem_proved",
    "full_localized_source_theorem_proved",
    "full_navier_stokes_theorem_proved",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
    "source_mechanism_promoted",
    "source_bound_proved",
    "source_emitter_promoted",
    "analytic_closure_promoted",
}
TRUE_PROMOTION_PATTERNS = (
    re.compile(
        r'"(?:bkm_finite|claim_closed|claim_proved|claim_proven|full_theorem_proved|'
        r'full_localized_source_theorem_proved|full_navier_stokes_theorem_proved|'
        r'full_clay_ns_solved|clay_navier_stokes_promoted|promotion_allowed|'
        r'source_mechanism_promoted|source_bound_proved|source_emitter_promoted|'
        r'analytic_closure_promoted)"'
        r"\s*:\s*true\b",
        re.IGNORECASE,
    ),
)


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


def discover_sprint153_scripts() -> list[Path]:
    return sorted(path for path in SCRIPT_DIR.glob("ns_sprint153_*.py") if path.is_file())


def bool_values_for_keys(values: list[Any], *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    found: list[bool] = []
    for item in walk(values):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted:
                parsed = as_bool(value)
                if parsed is not None:
                    found.append(parsed)
    return found


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    row_markers = {
        "row_id",
        "case_id",
        "scenario_id",
        "source_id",
        "status",
        "classification",
    }
    for item in walk(payloads):
        if isinstance(item, dict) and any(normalize(key) in row_markers for key in item):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def script_supports_arg(script: Path, arg: str) -> bool:
    text = script.read_text(encoding="utf-8", errors="replace")
    return f'"{arg}"' in text or f"'{arg}'" in text


def declared_string_set(script: Path, name: str) -> set[str]:
    tree = ast.parse(script.read_text(encoding="utf-8", errors="replace"))
    for node in tree.body:
        if not isinstance(node, ast.Assign):
            continue
        if not any(isinstance(target, ast.Name) and target.id == name for target in node.targets):
            continue
        value = ast.literal_eval(node.value)
        return {normalize(item) for item in value}
    return set()


def declared_required_row_ids(script: Path) -> set[str]:
    return declared_string_set(script, "REQUIRED_ROW_IDS")


def declared_classifications(script: Path) -> set[str]:
    return declared_string_set(script, "CLASSIFICATIONS")


def artifact_dir_for(script: Path, scratch_dir: Path) -> tuple[Path, list[str]]:
    stem = script.stem
    args: list[str] = []
    if script_supports_arg(script, "--repo-root"):
        args.extend(["--repo-root", str(REPO_ROOT)])
    if script_supports_arg(script, "--out-dir"):
        out_dir = scratch_dir / stem
        args.extend(["--out-dir", str(out_dir)])
        return out_dir, args
    return OUTPUTS_DIR / stem, args


def load_artifacts(out_dir: Path) -> tuple[list[Any], list[Path], list[Path], list[Path], str]:
    artifact_paths = sorted(path for path in out_dir.glob("*") if path.is_file())
    json_paths = [path for path in artifact_paths if path.suffix.lower() == ".json"]
    csv_paths = [path for path in artifact_paths if path.suffix.lower() == ".csv"]
    md_paths = [path for path in artifact_paths if path.suffix.lower() == ".md"]
    text = "\n".join(
        path.read_text(encoding="utf-8", errors="replace")
        for path in [*json_paths, *csv_paths, *md_paths]
    )
    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    return payloads, json_paths, csv_paths, md_paths, text


def run_emitter(script: Path, scratch_dir: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
    out_dir, extra_args = artifact_dir_for(script, scratch_dir)
    result = subprocess.run(
        [sys.executable, str(script), *extra_args],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    payloads: list[Any] = []
    json_paths: list[Path] = []
    csv_paths: list[Path] = []
    md_paths: list[Path] = []
    artifact_text = ""
    if out_dir.exists():
        payloads, json_paths, csv_paths, md_paths, artifact_text = load_artifacts(out_dir)

    text = "\n".join([result.stdout, result.stderr, artifact_text])
    assert result.returncode == 0, text
    assert out_dir.is_dir(), text
    assert json_paths, text
    assert csv_paths, text
    assert md_paths, text
    assert all(path.stat().st_size > 0 for path in [*json_paths, *csv_paths, *md_paths])
    assert any("summary" in path.name for path in json_paths), [path.name for path in json_paths]
    assert any(("rows" in path.name or "ledger" in path.name) for path in [*json_paths, *csv_paths]), [
        path.name for path in [*json_paths, *csv_paths]
    ]
    assert any("manifest" in path.name for path in json_paths), [path.name for path in json_paths]
    assert all(script.stem in path.name for path in [*json_paths, *csv_paths, *md_paths])

    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, text
    return payloads, rows, text, out_dir


def row_ids(rows: list[dict[str, Any]]) -> set[str]:
    return {
        normalize(row["row_id"])
        for row in rows
        if isinstance(row.get("row_id"), str) and row["row_id"].strip()
    }


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


def assert_control_card(payloads: list[Any], text: str) -> None:
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        if CONTROL_CARD_KEYS.issubset({str(key) for key in item}):
            return
        card = item.get("control_card") or item.get("control-card")
        if isinstance(card, dict) and CONTROL_CARD_KEYS.issubset({str(key) for key in card}):
            return
    normalized_text = normalize(text)
    missing = [key for key in CONTROL_CARD_KEYS if normalize(key) not in normalized_text]
    assert not missing, f"missing control-card keys {missing}\n{text}"


def assert_promotion_guards_false(payloads: list[Any], rows: list[dict[str, Any]], text: str) -> None:
    guard_values: list[bool] = []
    for name in FALSE_GUARD_NAMES:
        values = bool_values_for_keys([payloads, rows], name)
        if values:
            assert all(value is False for value in values), (name, values)
            guard_values.extend(values)

    for item in walk([payloads, rows]):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            key_text = normalize(key)
            if (
                "promot" in key_text
                or key_text in {
                    "bkm_finite",
                    "clay_ns_solved",
                    "full_clay_ns_solved",
                    "full_navier_stokes_theorem_proved",
                    "full_theorem_proved",
                }
                or (key_text.endswith("_proved") and "support" not in key_text)
                or key_text.endswith("_proven")
            ):
                parsed = as_bool(value)
                if parsed is not None:
                    assert parsed is False, (key, value)
                    guard_values.append(parsed)

    assert guard_values, f"missing promotion guard flags\n{text}"
    for pattern in TRUE_PROMOTION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_sprint153_expected_lane_source_emitters_are_present() -> None:
    scripts = discover_sprint153_scripts()
    assert len(scripts) == 3, [path.name for path in scripts]


def test_sprint153_source_emitters_record_rows_flags_and_fail_closed_guards(
    tmp_path: Path,
) -> None:
    scripts = discover_sprint153_scripts()
    assert len(scripts) == 3, [path.name for path in scripts]

    observed_lanes: set[int] = set()
    scratch_dir = OUTPUTS_DIR / ".pytest_ns_sprint153_source_emitters" / tmp_path.name
    if scratch_dir.exists():
        shutil.rmtree(scratch_dir)
    scratch_dir.mkdir(parents=True)
    try:
        for script in scripts:
            payloads, rows, text, out_dir = run_emitter(script, scratch_dir)

            assert out_dir.name == script.stem
            assert f"ns_sprint{SPRINT}" in script.stem
            assert len(row_ids(rows)) >= 3, text
            required_ids = declared_required_row_ids(script)
            ids = row_ids(rows)
            if required_ids:
                assert required_ids <= ids, sorted(required_ids - ids)
            classifications = {
                normalize(row["classification"])
                for row in rows
                if isinstance(row.get("classification"), str) and row["classification"].strip()
            }
            if classifications:
                expected_classifications = declared_classifications(script)
                if expected_classifications:
                    assert expected_classifications <= classifications, classifications
                else:
                    assert len(classifications) >= 2, classifications
            assert_control_card(payloads, text)
            assert_promotion_guards_false(payloads, rows, text)

            lanes = lane_values([payloads, rows])
            assert len(lanes) == 1, lanes
            lane = next(iter(lanes))
            assert lane in EXPECTED_LANES
            observed_lanes.add(lane)

            sprint_values = {
                item["sprint"]
                for item in walk([payloads, rows])
                if isinstance(item, dict) and item.get("sprint") in {SPRINT, str(SPRINT)}
            }
            assert sprint_values, text
    finally:
        shutil.rmtree(scratch_dir, ignore_errors=True)

    assert observed_lanes == EXPECTED_LANES
