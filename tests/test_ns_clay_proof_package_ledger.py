from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_clay_proof_package_ledger.py"


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build_fixture_spec(repo_root: Path, statuses: list[str]) -> tuple[Path, list[Path]]:
    artifacts: list[Path] = []
    packages: list[dict[str, object]] = []

    for package_id, status in enumerate(statuses, start=1):
        artifact = repo_root / f"calc/pkg_{package_id}.json"
        if package_id == 1:
            payload = {"package": package_id, "status": status, "rows": [1, 2, 3]}
        elif package_id == 2:
            payload = {"package": package_id, "status": status, "open": True}
        elif package_id == 3:
            payload = ["closeable", package_id, status]
        else:
            payload = {"package": package_id, "status": status, "note": f"fixture-{package_id}"}
        write_json(artifact, payload)
        artifacts.append(artifact)
        packages.append(
            {
                "package_id": package_id,
                "package_name": f"fixture_{package_id}",
                "status": status,
                "artifacts": [str(artifact.relative_to(repo_root))],
            }
        )

    spec = repo_root / "proof_package_spec.json"
    write_json(spec, {"packages": packages})
    return spec, artifacts


def run_ledger(repo_root: Path, spec: Path, output: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(repo_root),
            "--spec",
            str(spec),
            "--json-output",
            str(output),
        ],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def test_ledger_emits_compact_fail_closed_json(tmp_path: Path) -> None:
    statuses = [
        "closeable",
        "open",
        "closeable",
        "open",
        "closeable",
        "open",
        "open",
        "closeable",
        "Clay",
        "open",
    ]
    spec, artifacts = build_fixture_spec(tmp_path, statuses)
    output = tmp_path / "ledger.json"
    expected_calc12 = {
        "calc": "Calc12",
        "route_selector": "statistical",
        "script": "scripts/ns_clay_calc12_route_selector.py",
        "selector_script": "scripts/ns_clay_calc12_route_selector.py",
        "pair_builder_script": "scripts/ns_clay_calc12_pair_builder.py",
        "power_law": "|<omega,e2>|^2 ~ C*g12^beta",
        "fitted_beta": "candidate-only fitted beta placeholder",
        "fitted_C": "candidate-only fitted C placeholder",
        "beta_CI_95": "95% CI placeholder; compare the interval to 1 for route selection",
        "r_squared": "candidate-only r_squared placeholder",
        "n_pairs_raw": 9,
        "n_pairs_used": 9,
        "min_g12_observed": "candidate-only minimum observed g12 placeholder",
        "decision": "inconclusive",
        "aggregate_decision": "inconclusive",
        "beta_decision_thresholds": {
            ">1": "regularity_consistent",
            "<1": "blowup_precursor",
            "CI straddles 1": "inconclusive",
        },
        "proof_blocking": False,
        "no_further_calcs_blocking": True,
    }
    expected_calc12_result_metadata = {
        "result_artifact_path": (
            "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"
        ),
        "beta": 2.2754974180523737,
        "beta_CI_95": [2.129779448947756, 2.4212153871569915],
        "r_squared": 0.13893110418597066,
        "aggregate_decision": "regularity_consistent",
    }

    result = run_ledger(tmp_path, spec, output)
    assert result.returncode == 0, result.stderr

    payload = json.loads(result.stdout)
    file_payload = json.loads(output.read_text(encoding="utf-8"))

    assert payload == file_payload
    assert payload["contract"] == "ns_clay_proof_package_ledger"
    assert payload["package_count"] == 10
    assert payload["promotion"] is False
    assert payload["theorem_promotion"] is False
    assert payload["validation_passed"] is True
    assert payload["status_counts"] == {"Clay": 1, "closeable": 4, "open": 5}
    assert payload["control_card"]["first_six_are_formalization"] is True
    assert payload["control_card"]["hard_theorem_count"] == 2
    assert payload["control_card"]["hard_theorems"] == [
        "KornLevelSet",
        "collapseImpossible",
    ]
    assert "formalization/standard packages" in payload["control_card"]["concise_regularit_route"]
    assert (
        payload["control_card"]["concise_regularity_route"]
        == payload["control_card"]["concise_regularit_route"]
    )
    assert payload["calc11_status"] == "complete_no_special_alignment"
    assert payload["empirical_diagnostics_complete"] is True
    assert payload["closeable_package_count"] == 7
    assert payload["no_further_calcs_blocking"] is True
    assert payload["proof_blocking"] is False
    assert payload["remaining_math_wall"] == ["KornLevelSet", "collapseImpossible"]
    assert payload["hard_wall_count"] == 2
    assert payload["hard_walls"] == ["KornLevelSet", "collapseImpossible"]
    assert payload["clay_hard_core"] == "collapseImpossible"
    assert payload["calc12_executable"] is True
    assert payload["calc12_non_blocking"] is True
    assert payload["calc12_pair_builder_script"] == "scripts/ns_clay_calc12_pair_builder.py"
    assert payload["calc12_selector_script"] == "scripts/ns_clay_calc12_route_selector.py"
    assert payload["calc12_result_metadata"] == expected_calc12_result_metadata
    assert payload["calc12_route_selector"] == expected_calc12
    assert payload["calc12_route_selector"]["script"] == "scripts/ns_clay_calc12_route_selector.py"
    assert payload["calc12_route_selector"]["selector_script"] == "scripts/ns_clay_calc12_route_selector.py"
    assert (
        payload["calc12_route_selector"]["pair_builder_script"]
        == "scripts/ns_clay_calc12_pair_builder.py"
    )
    assert payload["calc12_route_selector"]["fitted_beta"] == "candidate-only fitted beta placeholder"
    assert payload["calc12_route_selector"]["fitted_C"] == "candidate-only fitted C placeholder"
    assert (
        payload["calc12_route_selector"]["beta_CI_95"]
        == "95% CI placeholder; compare the interval to 1 for route selection"
    )
    assert payload["calc12_route_selector"]["r_squared"] == "candidate-only r_squared placeholder"
    assert payload["calc12_route_selector"]["n_pairs_raw"] == 9
    assert payload["calc12_route_selector"]["n_pairs_used"] == 9
    assert (
        payload["calc12_route_selector"]["min_g12_observed"]
        == "candidate-only minimum observed g12 placeholder"
    )
    assert payload["calc12_route_selector"]["decision"] == "inconclusive"
    assert payload["calc12_route_selector"]["aggregate_decision"] == "inconclusive"
    assert payload["formal_packages_write_now"] == [
        "millerToH5",
        "GD3-SobolevBound-Correct",
        "coareaGradientBound",
        "LocalConcentration",
        "pigeon_concentration",
        "StepA_PerComponent",
        "BoundaryHB_Correct",
    ]
    assert payload["boundaryHB_correct_status"] == "closeable"
    assert payload["boundaryHB_correct_dependency"] == [
        "pointwise_kornBiaxialBound",
        "nondegeneracy",
    ]
    assert payload["post_calc11"] == {
        "closeable_package_count": 7,
        "hard_wall_count": 2,
        "hard_walls": ["KornLevelSet", "collapseImpossible"],
        "clay_hard_core": "collapseImpossible",
        "calc12_executable": True,
        "calc12_non_blocking": True,
        "calc12_pair_builder_script": "scripts/ns_clay_calc12_pair_builder.py",
        "calc12_selector_script": "scripts/ns_clay_calc12_route_selector.py",
        "calc12_result_metadata": expected_calc12_result_metadata,
        "no_further_calcs_blocking": True,
        "optional_next_calc": {
            "calc": "Calc12",
            "route_selector": "statistical",
            "script": "scripts/ns_clay_calc12_route_selector.py",
            "selector_script": "scripts/ns_clay_calc12_route_selector.py",
            "pair_builder_script": "scripts/ns_clay_calc12_pair_builder.py",
            "power_law": "|<omega,e2>|^2 ~ C*g12^beta",
            "fitted_beta": "candidate-only fitted beta placeholder",
            "fitted_C": "candidate-only fitted C placeholder",
            "beta_CI_95": "95% CI placeholder; compare the interval to 1 for route selection",
            "r_squared": "candidate-only r_squared placeholder",
            "n_pairs_raw": 9,
            "n_pairs_used": 9,
            "min_g12_observed": "candidate-only minimum observed g12 placeholder",
            "decision": "inconclusive",
            "aggregate_decision": "inconclusive",
            "beta_decision_thresholds": {
                ">1": "regularity_consistent",
                "<1": "blowup_precursor",
                "CI straddles 1": "inconclusive",
            },
            "proof_blocking": False,
            "no_further_calcs_blocking": True,
            "blocking": False,
        },
    }
    assert payload["control_card"]["calc11_status"] == payload["calc11_status"]
    assert (
        payload["control_card"]["empirical_diagnostics_complete"]
        == payload["empirical_diagnostics_complete"]
    )
    assert payload["control_card"]["closeable_package_count"] == payload["closeable_package_count"]
    assert payload["control_card"]["no_further_calcs_blocking"] is True
    assert payload["control_card"]["remaining_math_wall"] == payload["remaining_math_wall"]
    assert payload["control_card"]["hard_wall_count"] == payload["hard_wall_count"]
    assert payload["control_card"]["hard_walls"] == payload["hard_walls"]
    assert payload["control_card"]["clay_hard_core"] == payload["clay_hard_core"]
    assert payload["control_card"]["calc12_executable"] is True
    assert payload["control_card"]["calc12_non_blocking"] is True
    assert (
        payload["control_card"]["calc12_pair_builder_script"]
        == "scripts/ns_clay_calc12_pair_builder.py"
    )
    assert (
        payload["control_card"]["calc12_selector_script"]
        == "scripts/ns_clay_calc12_route_selector.py"
    )
    assert payload["control_card"]["calc12_result_metadata"] == expected_calc12_result_metadata
    assert (
        payload["control_card"]["formal_packages_write_now"]
        == payload["formal_packages_write_now"]
    )
    assert payload["control_card"]["boundaryHB_correct_status"] == "closeable"
    assert (
        payload["control_card"]["boundaryHB_correct_dependency"]
        == payload["boundaryHB_correct_dependency"]
    )
    assert payload["control_card"]["calc11_next"] is False
    assert payload["control_card"]["calc11_next_legacy_field_retained"] is True
    assert payload["post_calc11"]["calc12_result_metadata"] == expected_calc12_result_metadata
    assert payload["control_card"]["post_calc11"] == payload["post_calc11"]
    assert payload["control_card"]["calc12_route_selector"] == expected_calc12
    assert payload["control_card"]["post_calc11"]["calc12_executable"] is True
    assert payload["control_card"]["post_calc11"]["calc12_non_blocking"] is True
    assert (
        payload["control_card"]["post_calc11"]["calc12_pair_builder_script"]
        == "scripts/ns_clay_calc12_pair_builder.py"
    )
    assert (
        payload["control_card"]["post_calc11"]["calc12_selector_script"]
        == "scripts/ns_clay_calc12_route_selector.py"
    )
    assert (
        payload["control_card"]["post_calc11"]["calc12_result_metadata"]
        == expected_calc12_result_metadata
    )
    assert payload["control_card"]["optional_next_calc_blocks_proof"] is False
    assert payload["control_card"]["proof_blocking"] is False
    assert payload["calc11_result_summary"] == {
        "bottom_5_percent_g12_mean_omega_e2_fraction": 0.343,
        "random_baseline": 1.0 / 3.0,
        "full_boundary_layer_mean": 0.432,
        "decision": "no_special_alignment",
    }
    assert payload["control_card"]["calc11_result_summary"] == payload["calc11_result_summary"]

    packages = payload["packages"]
    assert [row["package_id"] for row in packages] == list(range(1, 11))
    assert [row["status"] for row in packages] == statuses
    assert all(row["promotion"] is False for row in packages)
    assert all(row["theorem_promotion"] is False for row in packages)

    first_artifact = packages[0]["artifacts"][0]
    assert first_artifact["exists"] is True
    assert first_artifact["sha256"] == sha256(artifacts[0])
    assert first_artifact["kind"] == "dict"
    assert first_artifact["top_level_keys"] == ["package", "rows", "status"]

    third_artifact = packages[2]["artifacts"][0]
    assert third_artifact["kind"] == "list"
    assert third_artifact["item_count"] == 3


def test_ledger_fails_when_a_referenced_artifact_is_missing(tmp_path: Path) -> None:
    spec, _ = build_fixture_spec(
        tmp_path,
        [
            "closeable",
            "open",
            "closeable",
            "open",
            "closeable",
            "open",
            "open",
            "closeable",
            "Clay",
            "open",
        ],
    )
    missing = tmp_path / "calc" / "pkg_5.json"
    missing.unlink()
    output = tmp_path / "ledger.json"

    result = run_ledger(tmp_path, spec, output)
    assert result.returncode == 1
    assert "missing artifact" in result.stderr
    assert not output.exists()
