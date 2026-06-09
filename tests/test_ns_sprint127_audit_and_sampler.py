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


def sprint127_scripts() -> list[Path]:
    return sorted(SCRIPTS_DIR.glob("*_sprint127_*.py"))


def find_script(kind: str, required_terms: tuple[str, ...] = ()) -> Path:
    candidates = sprint127_scripts()
    matches = [
        path
        for path in candidates
        if path.stem.startswith("ns_")
        and kind in path.stem
        and all(term in path.stem for term in required_terms)
    ]
    assert matches, f"missing Sprint 127 {kind} script among {[path.name for path in candidates]}"
    assert len(matches) == 1, f"ambiguous Sprint 127 {kind} scripts: {[path.name for path in matches]}"
    return matches[0]


def run_script(script: Path, out_dir: Path, tmp_path: Path) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["TMPDIR"] = str(tmp_path)
    return subprocess.run(
        [sys.executable, str(script), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
        env=env,
    )


def artifact_paths(out_dir: Path) -> tuple[list[Path], list[Path], list[Path]]:
    return (
        sorted(out_dir.glob("*.json")),
        sorted(out_dir.glob("*.csv")),
        sorted(out_dir.glob("*.md")),
    )


def load_json(paths: list[Path]) -> list[Any]:
    return [json.loads(path.read_text(encoding="utf-8")) for path in paths]


def load_csv(paths: list[Path]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(csv.DictReader(handle))
    return rows


def summary_json_paths(paths: list[Path]) -> list[Path]:
    summaries = [path for path in paths if "summary" in path.name]
    assert summaries, f"missing summary JSON in {[path.name for path in paths]}"
    return summaries


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
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "compatible"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "open", "blocked", "hold"}:
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


def assert_scalar_false(payloads: list[Any], *names: str) -> None:
    values = [parsed for value in scalar_values(payloads, *names) if (parsed := boolish(value)) is not None]
    assert values, f"missing boolean-like field for {names}"
    assert values[-1] is False, values


def assert_scalar_true(payloads: list[Any], *names: str) -> None:
    values = [parsed for value in scalar_values(payloads, *names) if (parsed := boolish(value)) is not None]
    assert values, f"missing boolean-like field for {names}"
    assert values[-1] is True, values


def assert_positive_count(payloads: list[Any]) -> None:
    for name in (
        "compatible_count",
        "compatibleCount",
        "balance_compatible_count",
        "balanceCompatibleCount",
        "viable_balance_count",
        "viableBalanceCount",
    ):
        for value in reversed(scalar_values(payloads, name)):
            parsed = numberish(value)
            if parsed is not None and parsed > 0:
                return
    assert False, "missing positive compatible_count or viable_balance_count"


def row_matches_required_witness(row: dict[str, Any]) -> bool:
    normalized = {normalize_key(str(key)): value for key, value in row.items()}
    alpha = numberish(normalized.get("alphafraction", normalized.get("alpha")))
    beta = numberish(normalized.get("betafraction", normalized.get("beta")))
    gamma = numberish(normalized.get("gammafraction", normalized.get("gamma")))
    compatible = boolish(
        normalized.get(
            "compatible",
            normalized.get(
                "iscompatible",
                normalized.get(
                    "routecompatible",
                    normalized.get("balancecompatible", normalized.get("viable")),
                ),
            ),
        )
    )
    return alpha == Fraction(1, 1) and beta == Fraction(0, 1) and gamma == Fraction(4, 3) and compatible is True


def assert_required_witness_row(payloads: list[Any], csv_rows: list[dict[str, str]]) -> None:
    json_rows = [item for item in flatten(payloads) if isinstance(item, dict)]
    if any(row_matches_required_witness(row) for row in [*json_rows, *csv_rows]):
        return
    assert False, "missing compatible alpha=1 beta=0 gamma=4/3 row"


def assert_no_clay_promotion(payloads: list[Any]) -> None:
    assert_scalar_false(
        payloads,
        "clay",
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
        "clayPromoted",
        "clay_yang_mills_promoted",
        "clayYangMillsPromoted",
    )


def test_sprint127_worker2_audit_runs_and_passes(tmp_path: Path) -> None:
    script = find_script("audit", ("axisymmetric", "boundary"))
    out_dir = tmp_path / script.stem
    result = run_script(script, out_dir, tmp_path)

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"
    assert not csv_paths, "audit should not emit sampler CSV rows"
    assert result.returncode == 0, result.stdout + result.stderr

    payloads = load_json(json_paths)
    assert_scalar_true(payloads, "passed", "complete", "ledger_coherent_fail_closed")
    assert not scalar_values(payloads, "marker_failures") or scalar_values(payloads, "marker_failures") == [[]]
    assert_no_clay_promotion(payloads)


def test_sprint127_worker3_sampler_writes_outputs_and_required_row(tmp_path: Path) -> None:
    script = find_script("sampler")
    out_dir = tmp_path / script.stem
    result = run_script(script, out_dir, tmp_path)

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "sampler did not write JSON output"
    assert csv_paths, "sampler did not write CSV output"
    assert md_paths, "sampler did not write Markdown output"
    assert result.returncode == 0, result.stdout + result.stderr

    summaries = load_json(summary_json_paths(json_paths))
    payloads = load_json(json_paths)
    csv_rows = load_csv(csv_paths)
    assert_positive_count(summaries)
    assert_required_witness_row(payloads, csv_rows)
    assert_scalar_false(payloads, "proof_established", "proofEstablished")
    assert_no_clay_promotion(payloads)
