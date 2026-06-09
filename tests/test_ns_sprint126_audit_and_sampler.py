from __future__ import annotations

import csv
import json
import os
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = REPO_ROOT / "scripts"


def find_script(kind: str, required_terms: tuple[str, ...]) -> Path:
    candidates = sorted(SCRIPTS_DIR.glob("ns_sprint126*.py"))
    matches = [
        path
        for path in candidates
        if kind in path.stem and all(term in path.stem for term in required_terms)
    ]
    if not matches:
        matches = [
            path
            for path in candidates
            if all(term in path.stem for term in (kind, *required_terms))
        ]
    assert matches, f"missing Sprint 126 {kind} script among {[path.name for path in candidates]}"
    assert len(matches) == 1, f"ambiguous Sprint 126 {kind} scripts: {[path.name for path in matches]}"
    return matches[0]


def run_script(script: Path, tmp_path: Path) -> subprocess.CompletedProcess[str]:
    out_dir = tmp_path / script.stem
    env = os.environ.copy()
    env["TMPDIR"] = str(tmp_path)
    result = subprocess.run(
        [sys.executable, str(script), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
        env=env,
    )
    return result


def artifact_paths(out_dir: Path) -> tuple[list[Path], list[Path], list[Path]]:
    return (
        sorted(out_dir.glob("*.json")),
        sorted(out_dir.glob("*.csv")),
        sorted(out_dir.glob("*.md")),
    )


def load_json(paths: list[Path]) -> list[Any]:
    return [json.loads(path.read_text(encoding="utf-8")) for path in paths]


def summary_json_paths(paths: list[Path]) -> list[Path]:
    summaries = [path for path in paths if "summary" in path.name]
    assert summaries, f"missing summary JSON in {[path.name for path in paths]}"
    return summaries


def load_csv(paths: list[Path]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(csv.DictReader(handle))
    return rows


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def normalize_key(key: str) -> str:
    return "".join(ch for ch in key.lower() if ch.isalnum())


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return value != 0
    if isinstance(value, str):
        lowered = value.strip().replace("_", "-").lower()
        if lowered in {"true", "1", "yes", "pass", "passed", "compatible", "closed"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "incompatible", "open", "hold"}:
            return False
    return None


def numberish(value: Any) -> Fraction | None:
    if isinstance(value, bool) or value is None or value == "":
        return None
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, float):
        return Fraction(str(value))
    if isinstance(value, str):
        text = value.strip()
        try:
            return Fraction(text)
        except ValueError:
            try:
                return Fraction(str(float(text)))
            except ValueError:
                return None
    return None


def scalar_values(payloads: list[Any], *names: str) -> list[Any]:
    wanted = {normalize_key(name) for name in names}
    values: list[Any] = []
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize_key(str(key)) in wanted and not isinstance(value, (dict, list)):
                values.append(value)
    return values


def scalar_bool(payloads: list[Any], *names: str) -> bool:
    values = [parsed for value in scalar_values(payloads, *names) if (parsed := boolish(value)) is not None]
    assert values, f"missing boolean-like field for {names}"
    return values[-1]


def scalar_int(payloads: list[Any], *names: str) -> int:
    values = scalar_values(payloads, *names)
    for value in reversed(values):
        parsed = numberish(value)
        if parsed is not None and parsed.denominator == 1:
            return int(parsed)
    assert False, f"missing integer-like field for {names}"


def assert_context_bool_false(payloads: list[Any], *context_terms: str) -> None:
    terms = [term.lower() for term in context_terms]
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        row_text = json.dumps(item, sort_keys=True).lower()
        if not all(term in row_text for term in terms):
            continue
        values = [
            boolish(value)
            for value in item.values()
            if not isinstance(value, (dict, list))
        ]
        if any(value is False for value in values):
            return
    assert False, f"missing false row containing {context_terms}"


def row_matches_compatibility(row: dict[str, Any]) -> bool:
    normalized = {normalize_key(str(key)): value for key, value in row.items()}
    alpha = numberish(normalized.get("alphafraction", normalized.get("alpha")))
    beta = numberish(normalized.get("betafraction", normalized.get("beta")))
    gamma = numberish(normalized.get("gammafraction", normalized.get("gamma")))
    compatible = boolish(
        normalized.get("compatible", normalized.get("iscompatible", normalized.get("routecompatible")))
    )
    return alpha == Fraction(1, 1) and beta == Fraction(0, 1) and gamma == Fraction(4, 3) and compatible is True


def assert_compatible_row(payloads: list[Any], csv_rows: list[dict[str, str]]) -> None:
    json_rows = [item for item in flatten(payloads) if isinstance(item, dict)]
    if any(row_matches_compatibility(row) for row in [*json_rows, *csv_rows]):
        return
    assert False, "missing compatible alpha=1 beta=0 gamma=4/3 row"


def test_sprint126_log_gap_audit_runs_and_passes(tmp_path: Path) -> None:
    script = find_script("audit", ("log", "gap"))
    result = run_script(script, tmp_path)

    out_dir = tmp_path / script.stem
    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"
    assert out_dir.exists()

    payloads = load_json(summary_json_paths(json_paths))
    all_payloads = load_json(json_paths)
    assert not csv_paths
    assert scalar_bool(
        payloads,
        "log_gap_audit_passed",
        "logGapAuditPassed",
        "log_gap_passed",
        "logGapPassed",
        "audit_passed",
        "passed",
    ) is True
    assert result.returncode == 0, result.stdout + result.stderr
    assert_context_bool_false(all_payloads, "clay", "promotion")


def test_sprint126_sampler_writes_compatible_summary_and_row(tmp_path: Path) -> None:
    script = find_script("sampler", ())
    result = run_script(script, tmp_path)

    out_dir = tmp_path / script.stem
    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "sampler did not write JSON output"
    assert csv_paths, "sampler did not write CSV output"
    assert md_paths, "sampler did not write Markdown output"
    assert out_dir.exists()
    assert result.returncode == 0, result.stdout + result.stderr

    summaries = load_json(summary_json_paths(json_paths))
    payloads = load_json(json_paths)
    csv_rows = load_csv(csv_paths)
    assert scalar_int(summaries, "compatible_count") > 0
    assert_compatible_row(payloads, csv_rows)
    assert scalar_bool(
        payloads,
        "clay",
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
        "clayPromoted",
    ) is False
