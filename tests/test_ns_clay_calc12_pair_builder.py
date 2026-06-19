from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import numpy as np
import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_clay_calc12_pair_builder.py"


def _require_script() -> None:
    if not SCRIPT.is_file():
        pytest.skip("ns_clay_calc12_pair_builder.py is not present yet")


def _write_fixture(
    path: Path,
    *,
    g12: list[float],
    lambda2: list[float],
    omega_e2_sq: list[float] | None = None,
    omega_e2_fraction: list[float] | None = None,
    omega_sq: list[float] | None = None,
    datum_id: str = "calc12-fixture",
) -> None:
    payload: dict[str, Any] = {
        "datum_id": np.array(datum_id),
        "g12": np.asarray(g12, dtype=np.float64),
        "lambda2": np.asarray(lambda2, dtype=np.float64),
    }
    if omega_e2_sq is not None:
        payload["omega_e2_sq"] = np.asarray(omega_e2_sq, dtype=np.float64)
    if omega_e2_fraction is not None:
        payload["omega_e2_fraction"] = np.asarray(omega_e2_fraction, dtype=np.float64)
    if omega_sq is not None:
        payload["omega_sq"] = np.asarray(omega_sq, dtype=np.float64)
    np.savez(path, **payload)


def _maybe_alt_flags(args: list[str]) -> list[str]:
    replacements = {
        "--input": "--json-input",
        "--output": "--json-output",
        "--lambda2-band": "--lambda2_band",
        "--max-pairs": "--max_pairs",
    }
    alt = [replacements.get(arg, arg) for arg in args]
    return alt


def _invoke_builder(argv: list[str]) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(
        argv,
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    combined = completed.stdout + completed.stderr
    if completed.returncode != 0 and "unrecognized arguments" in combined:
        alt = _maybe_alt_flags(argv)
        if alt != argv:
            completed = subprocess.run(
                alt,
                cwd=REPO_ROOT,
                check=False,
                capture_output=True,
                text=True,
            )
    return completed


def _run_builder(tmp_path: Path, input_path: Path, *extra_args: str) -> tuple[dict[str, Any], Path]:
    _require_script()
    output_path = tmp_path / "calc12_pairs.json"
    completed = _invoke_builder(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(input_path),
            "--output",
            str(output_path),
            *extra_args,
        ]
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert output_path.exists(), "builder did not write the requested output file"

    stdout_payload = json.loads(completed.stdout)
    file_payload = json.loads(output_path.read_text(encoding="utf-8"))
    assert stdout_payload == file_payload
    return file_payload, output_path


def _pair_entries(payload: dict[str, Any]) -> list[dict[str, Any]]:
    if "datasets" in payload:
        datasets = payload["datasets"]
        assert isinstance(datasets, list)
        assert len(datasets) == 1
        dataset = datasets[0]
        assert isinstance(dataset, dict)
        entries = dataset.get("pairs")
        assert isinstance(entries, list)
        assert entries, "dataset pairs must be a non-empty list"
        for entry in entries:
            assert isinstance(entry, dict), "dataset pair entries must be objects"
        return entries
    for key in ("pairs", "rows"):
        if key in payload:
            entries = payload[key]
            assert isinstance(entries, list)
            assert entries, f"{key} must be a non-empty list"
            for entry in entries:
                assert isinstance(entry, dict), f"{key} entries must be objects"
            return entries
    raise AssertionError("payload is missing a pair container such as 'pairs' or 'rows'")


def _sorted_g12_omega_pairs(payload: dict[str, Any]) -> list[tuple[float, float]]:
    entries = sorted(_pair_entries(payload), key=lambda row: float(row["g12"]))
    return [(float(row["g12"]), float(row["omega_e2_sq"])) for row in entries]


def test_pair_builder_uses_direct_omega_e2_sq_and_lambda2_band_filtering(tmp_path: Path) -> None:
    input_path = tmp_path / "direct_pairs_fixture.npz"
    _write_fixture(
        input_path,
        g12=[1.0, 2.0, 3.0, 4.0, 5.0],
        lambda2=[-0.02, 0.0, 0.02, 0.08, -0.09],
        omega_e2_sq=[10.0, 20.0, 30.0, 40.0, 50.0],
        datum_id="direct-omega-e2-sq",
    )

    payload, _ = _run_builder(tmp_path, input_path, "--lambda2-band", "0.05")
    assert _sorted_g12_omega_pairs(payload) == [
        (1.0, 10.0),
        (2.0, 20.0),
        (3.0, 30.0),
    ]


def test_pair_builder_computes_omega_e2_sq_from_fraction_times_omega_sq(tmp_path: Path) -> None:
    input_path = tmp_path / "computed_pairs_fixture.npz"
    _write_fixture(
        input_path,
        g12=[1.0, 2.0, 3.0, 4.0, 5.0],
        lambda2=[-0.02, 0.0, 0.02, 0.08, -0.09],
        omega_e2_fraction=[0.1, 0.2, 0.3, 0.4, 0.5],
        omega_sq=[10.0, 20.0, 30.0, 40.0, 50.0],
        datum_id="fraction-times-omega-sq",
    )

    payload, _ = _run_builder(tmp_path, input_path, "--lambda2-band", "0.05")
    assert _sorted_g12_omega_pairs(payload) == [
        (1.0, 1.0),
        (2.0, 4.0),
        (3.0, 9.0),
    ]


def test_pair_builder_rejects_missing_omega_fields_fail_closed(tmp_path: Path) -> None:
    _require_script()
    input_path = tmp_path / "missing_omega_fixture.npz"
    _write_fixture(
        input_path,
        g12=[1.0, 2.0, 3.0],
        lambda2=[0.0, 0.01, -0.01],
        datum_id="missing-omega-fields",
    )

    output_path = tmp_path / "calc12_pairs.json"
    completed = _invoke_builder(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(input_path),
            "--output",
            str(output_path),
        ]
    )

    assert completed.returncode != 0
    combined = completed.stdout + completed.stderr
    assert any(token in combined for token in ("omega_e2_sq", "omega_e2_fraction", "omega_sq"))


def test_pair_builder_max_pairs_is_deterministic(tmp_path: Path) -> None:
    input_path = tmp_path / "max_pairs_fixture.npz"
    _write_fixture(
        input_path,
        g12=[5.0, 1.0, 4.0, 2.0, 3.0],
        lambda2=[0.0, -0.01, 0.01, -0.02, 0.02],
        omega_e2_sq=[50.0, 10.0, 40.0, 20.0, 30.0],
        datum_id="max-pairs-determinism",
    )

    first_payload, _ = _run_builder(tmp_path, input_path, "--lambda2-band", "0.05", "--max-pairs", "3")
    second_payload, _ = _run_builder(tmp_path, input_path, "--lambda2-band", "0.05", "--max-pairs", "3")

    assert first_payload == second_payload
    assert len(_pair_entries(first_payload)) == 3
