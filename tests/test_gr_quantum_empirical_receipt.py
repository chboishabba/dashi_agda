from __future__ import annotations

import importlib.util
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "validate_gr_quantum_empirical_receipt.py"
SPEC = importlib.util.spec_from_file_location("gr_quantum_validator", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def _observable(name: str) -> dict[str, object]:
    return {
        "formal_source": f"formal:{name}",
        "measured_quantity": f"measured:{name}",
        "unit_symbol": "u",
        "unit_convention": "declared SI-compatible convention",
        "traceability_reference": "calibration-chain-1",
        "dataset_identifier": f"dataset-{name}",
        "dataset_revision": "v1",
        "calibration_artifact_hash": f"sha256:{name}",
        "uncertainty_model": "declared covariance model",
        "normalization_fixed": True,
        "held_out_calibration": True,
        "within_declared_tolerance": True,
        "uncertainty_propagated": True,
        "declared_tolerance": 0.1,
        "observed_error": 0.05,
    }


def _limit(name: str) -> dict[str, object]:
    return {
        "formal_regime": name,
        "reference_theory": "accepted reference theory",
        "reference_version": "v1",
        "derivation_artifact_hash": f"sha256:derive-{name}",
        "comparison_artifact_hash": f"sha256:compare-{name}",
        "continuum_or_asymptotic_authority": True,
        "agreement_within_error": True,
        "independent_reference_implementation": True,
        "no_evaluation_fit": True,
        "maximum_normalized_error": 0.01,
        "declared_error_tolerance": 0.02,
    }


def _benchmark(name: str) -> dict[str, object]:
    return {
        "candidate_solver": "DASHI candidate",
        "candidate_revision": "candidate-v1",
        "reference_solver": "reference solver",
        "reference_revision": "reference-v1",
        "hardware": "pinned hardware",
        "precision": "float64",
        "dataset_identifier": f"benchmark-{name}",
        "split_manifest_hash": f"sha256:split-{name}",
        "quality_metric": "normalized error",
        "artifact_hash": f"sha256:artifact-{name}",
        "held_out_evaluation": True,
        "matched_quality": True,
        "side_information_accounted": True,
        "no_test_leakage": True,
        "failed_cases_retained": True,
        "independent_rerun": True,
        "candidate_quality": 0.10,
        "reference_quality": 0.11,
        "quality_tolerance": 0.02,
        "candidate_runtime_seconds": 2.0,
        "reference_runtime_seconds": 3.0,
        "candidate_peak_memory_bytes": 1000,
        "reference_peak_memory_bytes": 1200,
    }


def _review(role: str, reviewer_id: str, commit: str) -> dict[str, object]:
    return {
        "reviewer_id": reviewer_id,
        "reviewer_name": f"Reviewer {role}",
        "affiliation": f"Independent institute {role}",
        "profile_or_contact": f"profile:{role}",
        "reviewed_commit": commit,
        "signed_report_reference": f"report:{role}",
        "artifact_manifest_hash": f"sha256:manifest-{role}",
        "conflict_declaration_reference": f"conflicts:{role}",
        "no_repository_authorship": True,
        "no_recent_direct_collaboration": True,
        "no_undisclosed_financial_conflict": True,
        "no_supervisory_dependency": True,
        "all_blocking_findings_resolved": True,
        "negative_cases_checked": True,
    }


def valid_receipt() -> dict[str, object]:
    commit = "0123456789abcdef0123456789abcdef01234567"
    observable_names = {
        "proper_time",
        "spatial_length",
        "energy",
        "transition_frequency",
        "probability",
        "curvature",
        "stress_energy",
    }
    limit_names = {
        "flat_special_relativity",
        "newtonian_weak_field_gravity",
        "vacuum_einstein_equation",
        "born_probability_rule",
        "free_field_heisenberg_ccr",
        "qft_on_curved_spacetime",
    }
    benchmark_names = {
        "weak_field_gr",
        "strong_field_gr",
        "free_quantum_dynamics",
        "qft_correlation",
        "joint_semiclassical_backreaction",
    }
    return {
        "schema_version": 1,
        "theory": {
            "commit_sha": commit,
            "parameter_manifest_hash": "sha256:parameters",
            "continuum_proof_artifact_hash": "sha256:continuum-proof",
            "continuum_authority_proved": True,
            "strict_terminal_typechecked": True,
            "no_hidden_postulates_audited": True,
        },
        "observables": {name: _observable(name) for name in observable_names},
        "known_limits": {name: _limit(name) for name in limit_names},
        "benchmarks": {name: _benchmark(name) for name in benchmark_names},
        "prediction": {
            "observable_name": "transition_frequency",
            "unit_symbol": "Hz",
            "theory_revision": commit,
            "parameter_manifest_hash": "sha256:parameters",
            "derivation_artifact_hash": "sha256:prediction",
            "preregistration_identifier": "registry:prediction-1",
            "rejection_criterion": "reject outside the declared confidence region",
            "systematics_budget_reference": "systematics:v1",
            "preregistered_before_observation": True,
            "uses_calibrated_observable": True,
            "statistical_power_declared": True,
            "can_reject_dashi": True,
            "can_reject_null": True,
            "no_post_hoc_parameter_adjustment": True,
            "null_and_adverse_results_publishable": True,
            "dashi_central_value": 1.2,
            "dashi_uncertainty": 0.1,
            "reference_central_value": 1.0,
            "reference_uncertainty": 0.1,
            "minimum_distinguishable_separation": 0.05,
        },
        "reviews": {
            "mathematics": _review("mathematics", "math-reviewer", commit),
            "physics": _review("physics", "physics-reviewer", commit),
            "replication": _review("replication", "replication-lead", commit),
        },
        "claims": {
            "physical_promotion_requested": True,
            "universal_superiority": False,
            "theory_of_everything": False,
        },
    }


def test_complete_receipt_passes() -> None:
    assert MODULE.validate(valid_receipt()) == []


def test_missing_observable_fails_closed() -> None:
    receipt = valid_receipt()
    del receipt["observables"]["curvature"]
    errors = MODULE.validate(receipt)
    assert any("observables missing" in error for error in errors)


def test_duplicate_reviewers_and_equal_prediction_fail() -> None:
    receipt = valid_receipt()
    receipt["reviews"]["physics"]["reviewer_id"] = "math-reviewer"
    receipt["prediction"]["reference_central_value"] = receipt["prediction"]["dashi_central_value"]
    errors = MODULE.validate(receipt)
    assert any("reviewer_id values must be distinct" in error for error in errors)
    assert "prediction central values must differ" in errors


def test_supervisory_dependency_fails_independence_gate() -> None:
    receipt = valid_receipt()
    receipt["reviews"]["mathematics"]["no_supervisory_dependency"] = False
    errors = MODULE.validate(receipt)
    assert "reviews.mathematics.no_supervisory_dependency must be true" in errors
