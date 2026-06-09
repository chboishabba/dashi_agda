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
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint129_feasibility_window_sampler.py"


def run_sampler(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], Path]:
    out_dir = tmp_path / SCRIPT.stem
    env = os.environ.copy()
    env["TMPDIR"] = str(tmp_path)
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
        env=env,
    )
    return result, out_dir


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
            rows.extend({"_csv_name": path.name, **row} for row in csv.DictReader(handle))
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
        if lowered in {"true", "1", "yes", "pass", "passed", "viable", "ok"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "blocked", "inviable", "not-viable"}:
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


def summary_payloads(json_paths: list[Path]) -> list[Any]:
    summaries = [path for path in json_paths if "summary" in path.name.lower()]
    assert summaries, f"missing summary JSON in {[path.name for path in json_paths]}"
    return load_json(summaries)


def all_text(paths: list[Path]) -> str:
    return "\n".join(path.read_text(encoding="utf-8") for path in paths)


def combined_rows(payloads: list[Any], csv_rows: list[dict[str, str]]) -> list[dict[str, Any]]:
    json_rows = [item for item in flatten(payloads) if isinstance(item, dict)]
    return [*json_rows, *csv_rows]


def row_alpha(row: dict[str, Any]) -> Fraction | None:
    normalized = {normalize_key(str(key)): value for key, value in row.items()}
    return numberish(normalized.get("alpha", normalized.get("alphafraction")))


def row_beta(row: dict[str, Any]) -> Fraction | None:
    normalized = {normalize_key(str(key)): value for key, value in row.items()}
    return numberish(normalized.get("beta", normalized.get("betafraction")))


def row_viable(row: dict[str, Any]) -> bool | None:
    normalized = {normalize_key(str(key)): value for key, value in row.items()}
    for key in (
        "viable",
        "isviable",
        "feasible",
        "isfeasible",
        "windowviable",
        "viscousfeasible",
        "allstrictgatespass",
        "strictgatespass",
    ):
        if key in normalized:
            return boolish(normalized[key])
    return None


def strict_gate_values(row: dict[str, Any]) -> list[bool]:
    normalized = {normalize_key(str(key)): value for key, value in row.items()}
    gates: list[bool] = []
    for key, value in normalized.items():
        is_gate_field = (
            "strict" in key
            or "gate" in key
            or key
            in {
                "bkmdivergencesurvives",
                "concentrationsurvives",
                "u1viscositysurvives",
                "nseconsistent",
                "inrecommendedalphawindow",
            }
        )
        if not is_gate_field:
            continue
        parsed = boolish(value)
        if parsed is not None:
            gates.append(parsed)
    return gates


def test_sprint129_feasibility_window_sampler_script_exists() -> None:
    assert SCRIPT.exists(), f"missing sampler script: {SCRIPT.relative_to(REPO_ROOT)}"


def test_sprint129_feasibility_window_sampler_cli_outputs_fail_closed(
    tmp_path: Path,
) -> None:
    assert SCRIPT.exists(), f"missing sampler script: {SCRIPT.relative_to(REPO_ROOT)}"
    result, out_dir = run_sampler(tmp_path)

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert result.returncode == 1, result.stdout + result.stderr
    assert json_paths, "sampler did not write JSON output"
    assert summary_payloads(json_paths)
    assert csv_paths, "sampler did not write CSV rows output"
    assert md_paths, "sampler did not write Markdown report"
    assert any("row" in path.name.lower() for path in csv_paths), [
        path.name for path in csv_paths
    ]

    payloads = load_json(json_paths)
    assert scalar_bool(
        payloads,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
        "clayPromoted",
    ) is False
    report = all_text(md_paths).lower()
    assert "viscous feasibility window" in report


def test_sprint129_viable_rows_are_exact_viscous_window_interior(
    tmp_path: Path,
) -> None:
    assert SCRIPT.exists(), f"missing sampler script: {SCRIPT.relative_to(REPO_ROOT)}"
    result, out_dir = run_sampler(tmp_path)
    assert result.returncode == 1, result.stdout + result.stderr

    json_paths, csv_paths, _md_paths = artifact_paths(out_dir)
    rows = combined_rows(load_json(json_paths), load_csv(csv_paths))
    viable_rows = [row for row in rows if row_viable(row) is True and row_alpha(row) is not None]
    assert viable_rows, "sampler did not record any viable rows"

    for row in viable_rows:
        alpha = row_alpha(row)
        beta = row_beta(row)
        assert alpha is not None
        assert beta is not None
        assert Fraction(1, 1) < alpha < Fraction(3, 2), row
        assert beta == alpha - 1, row


def test_sprint129_boundary_alphas_fail_strict_gate(
    tmp_path: Path,
) -> None:
    assert SCRIPT.exists(), f"missing sampler script: {SCRIPT.relative_to(REPO_ROOT)}"
    result, out_dir = run_sampler(tmp_path)
    assert result.returncode == 1, result.stdout + result.stderr

    json_paths, csv_paths, _md_paths = artifact_paths(out_dir)
    rows = combined_rows(load_json(json_paths), load_csv(csv_paths))
    boundary_rows = {
        alpha: [row for row in rows if row_alpha(row) == alpha]
        for alpha in (Fraction(1, 1), Fraction(3, 2))
    }

    for alpha, alpha_rows in boundary_rows.items():
        assert alpha_rows, f"missing boundary alpha={alpha} row"
        assert any(False in strict_gate_values(row) for row in alpha_rows), alpha_rows
