from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "sphere_unwrap_benchmark.py"


def run_benchmark(tmp_path: Path) -> dict[str, Any]:
    out_dir = tmp_path / "sphere_unwrap"
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--width",
            "12",
            "--height",
            "6",
            "--healpix-nside",
            "2",
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    stdout_payload = json.loads(proc.stdout)
    file_payload = json.loads(
        (out_dir / "sphere_unwrap_benchmark_summary.json").read_text(
            encoding="utf-8"
        )
    )
    assert stdout_payload == file_payload
    return stdout_payload


def test_adversarial_field_suite_emits_declared_receipts(tmp_path: Path) -> None:
    payload = run_benchmark(tmp_path)

    assert payload["benchmark"] == "adversarial_sphere_unwrap_fields"
    assert payload["grid"] == {"width": 12, "height": 6, "healpix_nside": 2}
    assert payload["claim_boundary"]["global_optimum"] is False
    assert payload["claim_boundary"]["isometry"] is False
    assert payload["claim_boundary"]["true_inverse"] is False
    assert set(payload["receipt_hashes"]) == {
        "harness_source_hash",
        "artifact_schema_hash",
        "command_hash",
        "environment_hash",
        "metrics_hash",
        "artifact_hash",
    }
    assert all(
        len(value) == 64 for value in payload["receipt_hashes"].values()
    )

    fields = {result["field"]: result for result in payload["field_results"]}
    assert set(fields) == {
        "constant",
        "linear_xyz",
        "low_frequency_harmonic",
        "high_frequency_harmonic",
        "polar_cap",
        "longitude_seam_stripe",
        "checkerboard_geodesic",
        "localized_gaussian_bump",
        "binary_hemisphere",
        "band_limited_mix",
    }
    assert sum(payload["winner_histogram"].values()) == len(fields)

    for result in fields.values():
        candidates = {c["method"]: c for c in result["candidates"]}
        assert {
            "bt369",
            "equal_area",
            "equirect",
            "cubed_sphere",
            "octahedral",
            "healpix",
            "xatlas",
        }.issubset(candidates)
        assert result["winner"] in candidates
        assert candidates["bt369"]["measured"] is True
        assert candidates["equal_area"]["measured"] is True
        assert candidates["equirect"]["measured"] is True
        assert candidates["cubed_sphere"]["measured"] is True
        assert candidates["octahedral"]["measured"] is True
        assert candidates["xatlas"]["measured"] is False
        assert candidates["xatlas"]["severity"] == 2
        assert (
            candidates["xatlas"]["claim_boundary"]["manufacturing_authority"]
            is False
        )


def test_bt369_receipt_carries_adaptive_369_certificate(tmp_path: Path) -> None:
    payload = run_benchmark(tmp_path)
    first = payload["field_results"][0]
    candidates = {c["method"]: c for c in first["candidates"]}
    bt369 = candidates["bt369"]

    assert bt369["available"] is True
    assert bt369["severity"] == 0
    assert bt369["metrics"]["foldover_count"] == 0
    assert bt369["certificate"]["prototype"] is True
    assert "trit_histogram" in bt369["certificate"]
    assert "depth_histogram" in bt369["certificate"]
    assert bt369["certificate"]["seam_braid_tokens"] >= 1
    assert bt369["claim_boundary"]["best_declared_candidate_only"] is True
    assert bt369["claim_boundary"]["seameinit_production_promotion"] is False


def test_healpix_is_measured_only_when_optional_dependency_imports(
    tmp_path: Path,
) -> None:
    payload = run_benchmark(tmp_path)
    first = payload["field_results"][0]
    healpix = {c["method"]: c for c in first["candidates"]}["healpix"]

    if healpix["available"]:
        assert healpix["measured"] is True
        assert healpix["metrics"]["area_residual"] == 0.0
        assert healpix["certificate"]["carrier"] == "equal_area_hierarchical_pixels"
    else:
        assert healpix["measured"] is False
        assert healpix["severity"] == 2
        assert "healpy unavailable" in healpix["unavailable_reason"]
