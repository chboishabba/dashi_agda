from __future__ import annotations

import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_clay_calc12_route_selector.py"


def pick(payload: dict[str, Any], *names: str) -> Any:
    for name in names:
        if name in payload:
            return payload[name]
    raise AssertionError(f"missing expected key: one of {', '.join(names)}")


def write_input_payload(tmp_path: Path, payload: dict[str, Any], name: str) -> tuple[Path, Path]:
    input_path = tmp_path / f"{name}.json"
    output_path = tmp_path / f"{name}_out.json"
    input_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return input_path, output_path


def run_selector(tmp_path: Path, rows: list[dict[str, Any]], name: str) -> dict[str, Any]:
    return run_selector_payload(tmp_path, {"datum_id": name, "pairs": rows}, name)


def run_selector_payload(tmp_path: Path, payload: dict[str, Any], name: str) -> dict[str, Any]:
    if not SCRIPT.exists():
        pytest.skip(f"missing {SCRIPT}")

    input_path, output_path = write_input_payload(tmp_path, payload, name)

    def invoke(*flags: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(SCRIPT), *flags],
            cwd=REPO_ROOT,
            check=False,
            text=True,
            capture_output=True,
        )

    result = invoke("--input", str(input_path), "--output", str(output_path))
    if result.returncode != 0 and "unrecognized arguments" in (result.stdout + result.stderr):
        result = invoke(
            "--json-input",
            str(input_path),
            "--json-output",
            str(output_path),
        )
    assert result.returncode == 0, result.stdout + result.stderr
    assert output_path.exists()

    stdout_payload = json.loads(result.stdout)
    file_payload = json.loads(output_path.read_text(encoding="utf-8"))
    assert stdout_payload == file_payload
    return file_payload


def run_selector_expect_failure(
    tmp_path: Path,
    payload: dict[str, Any],
    name: str,
) -> subprocess.CompletedProcess[str]:
    if not SCRIPT.exists():
        pytest.skip(f"missing {SCRIPT}")

    input_path, output_path = write_input_payload(tmp_path, payload, name)

    def invoke(*flags: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                *flags,
            ],
            cwd=REPO_ROOT,
            check=False,
            text=True,
            capture_output=True,
        )

    result = invoke("--input", str(input_path), "--output", str(output_path))
    if result.returncode != 0 and "unrecognized arguments" in (result.stdout + result.stderr):
        result = invoke(
            "--json-input",
            str(input_path),
            "--json-output",
            str(output_path),
        )
    return result


def valid_power_law_rows(beta: float, scale: float = 2.0, count: int = 5) -> list[dict[str, Any]]:
    g12_values = [0.25 * (2**idx) for idx in range(count)]
    return [
        {
            "g12": g12,
            "omega_e2_sq": scale * math.pow(g12, beta),
        }
        for g12 in g12_values
    ]


def assert_false_promotion_flags(payload: dict[str, Any]) -> None:
    assert pick(payload, "theorem_authority") is False
    assert pick(payload, "clay_promotion") is False
    assert pick(payload, "proof_blocking") is False


def first_dataset(payload: dict[str, Any]) -> dict[str, Any]:
    assert isinstance(payload["datasets"], list)
    assert len(payload["datasets"]) == 1
    return payload["datasets"][0]


def test_ns_clay_calc12_route_selector_regularity_consistent(tmp_path: Path) -> None:
    payload = run_selector(tmp_path, valid_power_law_rows(beta=1.5), "regularity")
    dataset = first_dataset(payload)
    fit = dataset["fit"]

    assert pick(payload, "route_selector") == "statistical"
    assert payload["aggregate_decision"] == "regularity_consistent"
    assert fit["decision"] == "regularity_consistent"
    assert dataset["n_pairs_raw"] == 5
    assert dataset["n_pairs_used"] == 5
    assert fit["beta"] > 1.0
    assert fit["beta_CI_95"][0] > 1.0
    assert fit["beta_CI_95"][1] >= fit["beta_CI_95"][0]
    assert_false_promotion_flags(payload)


def test_ns_clay_calc12_route_selector_blowup_precursor_filters_invalid_pairs(
    tmp_path: Path,
) -> None:
    rows = valid_power_law_rows(beta=0.5)
    rows.extend(
        [
            {"g12": -1.0, "omega_e2_sq": 0.1},
            {"g12": 0.0, "omega_e2_sq": 0.25},
            {"g12": 1.0, "omega_e2_sq": -0.1},
            {"g12": "bad", "omega_e2_sq": 0.5},
            {"g12": 2.0},
        ]
    )

    payload = run_selector(tmp_path, rows, "blowup")
    dataset = first_dataset(payload)
    fit = dataset["fit"]

    assert pick(payload, "route_selector") == "statistical"
    assert payload["aggregate_decision"] == "blowup_precursor"
    assert fit["decision"] == "blowup_precursor"
    assert dataset["n_pairs_raw"] == 10
    assert dataset["n_pairs_used"] == 5
    assert dataset["n_pairs_used"] < dataset["n_pairs_raw"]
    assert fit["beta"] < 1.0
    assert fit["beta_CI_95"][1] < 1.0
    assert_false_promotion_flags(payload)


def test_ns_clay_calc12_route_selector_inconclusive_for_mixed_signal(tmp_path: Path) -> None:
    rows = [
        {"g12": 0.25, "omega_e2_sq": 2.0 * math.pow(0.25, 0.8)},
        {"g12": 0.5, "omega_e2_sq": 2.0 * math.pow(0.5, 0.8)},
        {"g12": 1.0, "omega_e2_sq": 2.0},
        {"g12": 2.0, "omega_e2_sq": 2.0 * math.pow(2.0, 1.2)},
        {"g12": 4.0, "omega_e2_sq": 2.0 * math.pow(4.0, 1.2)},
    ]

    payload = run_selector(tmp_path, rows, "mixed")
    dataset = first_dataset(payload)
    fit = dataset["fit"]

    assert pick(payload, "route_selector") == "statistical"
    assert payload["aggregate_decision"] == "inconclusive"
    assert fit["decision"] == "inconclusive"
    low = fit["beta_CI_95"][0]
    high = fit["beta_CI_95"][1]
    assert low <= 1.0 <= high
    assert_false_promotion_flags(payload)


def test_ns_clay_calc12_route_selector_aggregate_blowup_precursor_wins(tmp_path: Path) -> None:
    payload = run_selector_payload(
        tmp_path,
        {
            "datasets": [
                {"datum_id": "regularity", "pairs": valid_power_law_rows(beta=1.4)},
                {
                    "datum_id": "blowup",
                    "pairs": [
                        {"g12": 0.25, "omega_e2_sq": 2.0 * math.pow(0.25, 0.6)},
                        {"g12": 0.5, "omega_e2_sq": 2.0 * math.pow(0.5, 0.6)},
                        {"g12": 1.0, "omega_e2_sq": 2.0},
                        {"g12": 2.0, "omega_e2_sq": 2.0 * math.pow(2.0, 0.4)},
                        {"g12": 4.0, "omega_e2_sq": 2.0 * math.pow(4.0, 0.4)},
                    ],
                },
            ]
        },
        "aggregate_blowup",
    )

    assert payload["aggregate_decision"] == "blowup_precursor"
    assert [dataset["fit"]["decision"] for dataset in payload["datasets"]] == [
        "regularity_consistent",
        "blowup_precursor",
    ]
    assert_false_promotion_flags(payload)


def test_ns_clay_calc12_route_selector_aggregate_all_regular_promotes(tmp_path: Path) -> None:
    payload = run_selector_payload(
        tmp_path,
        {
            "datasets": [
                {"datum_id": "regularity_a", "pairs": valid_power_law_rows(beta=1.25)},
                {"datum_id": "regularity_b", "pairs": valid_power_law_rows(beta=1.8)},
            ]
        },
        "aggregate_regular",
    )

    assert payload["aggregate_decision"] == "regularity_consistent"
    assert [dataset["fit"]["decision"] for dataset in payload["datasets"]] == [
        "regularity_consistent",
        "regularity_consistent",
    ]
    assert_false_promotion_flags(payload)


def test_ns_clay_calc12_route_selector_aggregate_mixed_regular_and_inconclusive_is_inconclusive(
    tmp_path: Path,
) -> None:
    payload = run_selector_payload(
        tmp_path,
        {
            "datasets": [
                {"datum_id": "regularity", "pairs": valid_power_law_rows(beta=1.3)},
                {
                    "datum_id": "inconclusive",
                    "pairs": [
                        {"g12": 0.25, "omega_e2_sq": 2.0 * math.pow(0.25, 0.8)},
                        {"g12": 0.5, "omega_e2_sq": 2.0 * math.pow(0.5, 0.8)},
                        {"g12": 1.0, "omega_e2_sq": 2.0},
                        {"g12": 2.0, "omega_e2_sq": 2.0 * math.pow(2.0, 1.2)},
                        {"g12": 4.0, "omega_e2_sq": 2.0 * math.pow(4.0, 1.2)},
                    ],
                },
            ]
        },
        "aggregate_mixed",
    )

    assert payload["aggregate_decision"] == "inconclusive"
    assert [dataset["fit"]["decision"] for dataset in payload["datasets"]] == [
        "regularity_consistent",
        "inconclusive",
    ]
    assert_false_promotion_flags(payload)


def test_ns_clay_calc12_route_selector_identical_positive_g12_values_fail_closed(
    tmp_path: Path,
) -> None:
    result = run_selector_expect_failure(
        tmp_path,
        {
            "datum_id": "identical_g12",
            "pairs": [
                {"g12": 2.0, "omega_e2_sq": 1.0},
                {"g12": 2.0, "omega_e2_sq": 1.5},
                {"g12": 2.0, "omega_e2_sq": 2.0},
            ],
        },
        "identical_positive_g12",
    )

    assert result.returncode != 0
    assert "g12 values must not all be identical" in (result.stdout + result.stderr)


def test_ns_clay_calc12_route_selector_accepts_parallel_array_input(
    tmp_path: Path,
) -> None:
    rows = valid_power_law_rows(beta=1.4)
    payload = {
        "datum_id": "array_form",
        "g12": [row["g12"] for row in rows],
        "omega_e2_sq": [row["omega_e2_sq"] for row in rows],
    }

    result = run_selector_payload(tmp_path, payload, "array_form")
    dataset = first_dataset(result)
    fit = dataset["fit"]

    assert pick(result, "route_selector") == "statistical"
    assert result["aggregate_decision"] == "regularity_consistent"
    assert fit["decision"] == "regularity_consistent"
    assert dataset["n_pairs_raw"] == 5
    assert dataset["n_pairs_used"] == 5
    assert_false_promotion_flags(result)


def test_ns_clay_calc12_route_selector_rejects_mixed_pairs_and_array_fields(
    tmp_path: Path,
) -> None:
    result = run_selector_expect_failure(
        tmp_path,
        {
            "datum_id": "mixed_forms",
            "pairs": valid_power_law_rows(beta=1.2),
            "g12": [0.25, 0.5, 1.0, 2.0, 4.0],
            "omega_e2_sq": [
                2.0 * math.pow(0.25, 1.2),
                2.0 * math.pow(0.5, 1.2),
                2.0,
                2.0 * math.pow(2.0, 1.2),
                2.0 * math.pow(4.0, 1.2),
            ],
        },
        "mixed_forms",
    )

    assert result.returncode != 0
    assert "provides both pairs and array fields; choose one form" in (
        result.stdout + result.stderr
    )


def test_ns_clay_calc12_route_selector_rejects_malformed_top_level_datasets(
    tmp_path: Path,
) -> None:
    result = run_selector_expect_failure(
        tmp_path,
        {"datasets": "not-a-list"},
        "malformed_datasets",
    )

    assert result.returncode != 0
    assert "top-level datasets must be a non-empty list" in (result.stdout + result.stderr)


def test_ns_clay_calc12_route_selector_rejects_too_few_positive_filtered_pairs(
    tmp_path: Path,
) -> None:
    result = run_selector_expect_failure(
        tmp_path,
        {
            "datum_id": "too_few_positive",
            "pairs": [
                {"g12": 0.25, "omega_e2_sq": 2.0 * math.pow(0.25, 1.1)},
                {"g12": 0.5, "omega_e2_sq": 2.0 * math.pow(0.5, 1.1)},
                {"g12": 0.0, "omega_e2_sq": 1.0},
                {"g12": 1.0, "omega_e2_sq": -1.0},
            ],
        },
        "too_few_positive",
    )

    assert result.returncode != 0
    assert "at least 3 finite positive pairs are required after filtering; got 2" in (
        result.stdout + result.stderr
    )
