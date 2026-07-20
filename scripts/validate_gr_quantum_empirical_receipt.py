#!/usr/bin/env python3
"""Validate a strict GR/quantum empirical correspondence receipt.

This validates evidence packaging and cross-lane coherence. It does not generate
measurements, prove continuum mathematics, or certify reviewer independence.
Those claims must already be backed by pinned external artifacts.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

REQUIRED_OBSERVABLES = {
    "proper_time",
    "spatial_length",
    "energy",
    "transition_frequency",
    "probability",
    "curvature",
    "stress_energy",
}

REQUIRED_LIMITS = {
    "flat_special_relativity",
    "newtonian_weak_field_gravity",
    "vacuum_einstein_equation",
    "born_probability_rule",
    "free_field_heisenberg_ccr",
    "qft_on_curved_spacetime",
}

REQUIRED_BENCHMARKS = {
    "weak_field_gr",
    "strong_field_gr",
    "free_quantum_dynamics",
    "qft_correlation",
    "joint_semiclassical_backreaction",
}

PLACEHOLDERS = {"", "todo", "tbd", "unknown", "placeholder", "none", "n/a"}


def _is_number(value: Any) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
    )


def _non_placeholder(value: Any) -> bool:
    return isinstance(value, str) and value.strip().lower() not in PLACEHOLDERS


def _require_true(block: dict[str, Any], key: str, path: str, errors: list[str]) -> None:
    if block.get(key) is not True:
        errors.append(f"{path}.{key} must be true")


def _require_string(block: dict[str, Any], key: str, path: str, errors: list[str]) -> None:
    if not _non_placeholder(block.get(key)):
        errors.append(f"{path}.{key} must be a non-placeholder string")


def _validate_observables(receipt: dict[str, Any], errors: list[str]) -> None:
    observables = receipt.get("observables")
    if not isinstance(observables, dict):
        errors.append("observables must be an object")
        return
    missing = REQUIRED_OBSERVABLES - set(observables)
    if missing:
        errors.append(f"observables missing {sorted(missing)}")
    for name in REQUIRED_OBSERVABLES & set(observables):
        block = observables[name]
        path = f"observables.{name}"
        if not isinstance(block, dict):
            errors.append(f"{path} must be an object")
            continue
        for key in (
            "formal_source",
            "measured_quantity",
            "unit_symbol",
            "unit_convention",
            "traceability_reference",
            "dataset_identifier",
            "dataset_revision",
            "calibration_artifact_hash",
            "uncertainty_model",
        ):
            _require_string(block, key, path, errors)
        for key in (
            "normalization_fixed",
            "held_out_calibration",
            "within_declared_tolerance",
            "uncertainty_propagated",
        ):
            _require_true(block, key, path, errors)
        for key in ("declared_tolerance", "observed_error"):
            value = block.get(key)
            if not _is_number(value) or value < 0:
                errors.append(f"{path}.{key} must be non-negative numeric")
        if _is_number(block.get("declared_tolerance")) and _is_number(block.get("observed_error")):
            if block["observed_error"] > block["declared_tolerance"]:
                errors.append(f"{path}.observed_error exceeds declared_tolerance")


def _validate_limits(receipt: dict[str, Any], errors: list[str]) -> None:
    limits = receipt.get("known_limits")
    if not isinstance(limits, dict):
        errors.append("known_limits must be an object")
        return
    missing = REQUIRED_LIMITS - set(limits)
    if missing:
        errors.append(f"known_limits missing {sorted(missing)}")
    for name in REQUIRED_LIMITS & set(limits):
        block = limits[name]
        path = f"known_limits.{name}"
        if not isinstance(block, dict):
            errors.append(f"{path} must be an object")
            continue
        for key in (
            "formal_regime",
            "reference_theory",
            "reference_version",
            "derivation_artifact_hash",
            "comparison_artifact_hash",
        ):
            _require_string(block, key, path, errors)
        for key in (
            "continuum_or_asymptotic_authority",
            "agreement_within_error",
            "independent_reference_implementation",
            "no_evaluation_fit",
        ):
            _require_true(block, key, path, errors)
        error_value = block.get("maximum_normalized_error")
        tolerance = block.get("declared_error_tolerance")
        if not _is_number(error_value) or error_value < 0:
            errors.append(f"{path}.maximum_normalized_error must be non-negative numeric")
        if not _is_number(tolerance) or tolerance < 0:
            errors.append(f"{path}.declared_error_tolerance must be non-negative numeric")
        if _is_number(error_value) and _is_number(tolerance) and error_value > tolerance:
            errors.append(f"{path}.maximum_normalized_error exceeds tolerance")


def _validate_benchmarks(receipt: dict[str, Any], errors: list[str]) -> None:
    benchmarks = receipt.get("benchmarks")
    if not isinstance(benchmarks, dict):
        errors.append("benchmarks must be an object")
        return
    missing = REQUIRED_BENCHMARKS - set(benchmarks)
    if missing:
        errors.append(f"benchmarks missing {sorted(missing)}")
    for name in REQUIRED_BENCHMARKS & set(benchmarks):
        block = benchmarks[name]
        path = f"benchmarks.{name}"
        if not isinstance(block, dict):
            errors.append(f"{path} must be an object")
            continue
        for key in (
            "candidate_solver",
            "candidate_revision",
            "reference_solver",
            "reference_revision",
            "hardware",
            "precision",
            "dataset_identifier",
            "split_manifest_hash",
            "quality_metric",
            "artifact_hash",
        ):
            _require_string(block, key, path, errors)
        for key in (
            "held_out_evaluation",
            "matched_quality",
            "side_information_accounted",
            "no_test_leakage",
            "failed_cases_retained",
            "independent_rerun",
        ):
            _require_true(block, key, path, errors)
        for key in (
            "candidate_quality",
            "reference_quality",
            "quality_tolerance",
            "candidate_runtime_seconds",
            "reference_runtime_seconds",
            "candidate_peak_memory_bytes",
            "reference_peak_memory_bytes",
        ):
            value = block.get(key)
            if not _is_number(value) or value < 0:
                errors.append(f"{path}.{key} must be non-negative numeric")
        if all(_is_number(block.get(key)) for key in ("candidate_quality", "reference_quality", "quality_tolerance")):
            if abs(block["candidate_quality"] - block["reference_quality"]) > block["quality_tolerance"]:
                errors.append(f"{path} quality values are not matched within tolerance")


def _validate_prediction(receipt: dict[str, Any], errors: list[str]) -> None:
    prediction = receipt.get("prediction")
    if not isinstance(prediction, dict):
        errors.append("prediction must be an object")
        return
    path = "prediction"
    for key in (
        "observable_name",
        "unit_symbol",
        "theory_revision",
        "parameter_manifest_hash",
        "derivation_artifact_hash",
        "preregistration_identifier",
        "rejection_criterion",
        "systematics_budget_reference",
    ):
        _require_string(prediction, key, path, errors)
    for key in (
        "preregistered_before_observation",
        "uses_calibrated_observable",
        "statistical_power_declared",
        "can_reject_dashi",
        "can_reject_null",
        "no_post_hoc_parameter_adjustment",
        "null_and_adverse_results_publishable",
    ):
        _require_true(prediction, key, path, errors)
    for key in (
        "dashi_central_value",
        "dashi_uncertainty",
        "reference_central_value",
        "reference_uncertainty",
        "minimum_distinguishable_separation",
    ):
        value = prediction.get(key)
        if not _is_number(value) or value < 0:
            errors.append(f"{path}.{key} must be non-negative numeric")
    if _is_number(prediction.get("dashi_central_value")) and _is_number(prediction.get("reference_central_value")):
        if prediction["dashi_central_value"] == prediction["reference_central_value"]:
            errors.append("prediction central values must differ")


def _validate_reviews(receipt: dict[str, Any], errors: list[str]) -> None:
    reviews = receipt.get("reviews")
    if not isinstance(reviews, dict):
        errors.append("reviews must be an object")
        return
    ids: list[str] = []
    commits: list[str] = []
    for role in ("mathematics", "physics", "replication"):
        block = reviews.get(role)
        path = f"reviews.{role}"
        if not isinstance(block, dict):
            errors.append(f"{path} must be an object")
            continue
        for key in (
            "reviewer_id",
            "reviewer_name",
            "affiliation",
            "profile_or_contact",
            "reviewed_commit",
            "signed_report_reference",
            "artifact_manifest_hash",
            "conflict_declaration_reference",
        ):
            _require_string(block, key, path, errors)
        for key in (
            "no_repository_authorship",
            "no_recent_direct_collaboration",
            "no_undisclosed_financial_conflict",
            "no_supervisory_dependency",
            "all_blocking_findings_resolved",
            "negative_cases_checked",
        ):
            _require_true(block, key, path, errors)
        ids.append(str(block.get("reviewer_id", "")))
        commits.append(str(block.get("reviewed_commit", "")))
    if len(ids) == 3 and len(set(ids)) != 3:
        errors.append("mathematics, physics, and replication reviewer_id values must be distinct")
    theory = receipt.get("theory", {})
    expected_commit = theory.get("commit_sha") if isinstance(theory, dict) else None
    if expected_commit and any(commit != expected_commit for commit in commits):
        errors.append("all review reviewed_commit values must equal theory.commit_sha")


def validate(receipt: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if receipt.get("schema_version") != 1:
        errors.append("schema_version must equal 1")

    theory = receipt.get("theory")
    if not isinstance(theory, dict):
        errors.append("theory must be an object")
    else:
        for key in ("commit_sha", "parameter_manifest_hash", "continuum_proof_artifact_hash"):
            _require_string(theory, key, "theory", errors)
        for key in ("continuum_authority_proved", "strict_terminal_typechecked", "no_hidden_postulates_audited"):
            _require_true(theory, key, "theory", errors)

    _validate_observables(receipt, errors)
    _validate_limits(receipt, errors)
    _validate_benchmarks(receipt, errors)
    _validate_prediction(receipt, errors)
    _validate_reviews(receipt, errors)

    claims = receipt.get("claims")
    if not isinstance(claims, dict):
        errors.append("claims must be an object")
    else:
        _require_true(claims, "physical_promotion_requested", "claims", errors)
        if claims.get("universal_superiority") is True:
            errors.append("claims.universal_superiority cannot follow from this receipt")
        if claims.get("theory_of_everything") is True:
            errors.append("claims.theory_of_everything cannot follow from empirical validation alone")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    try:
        data = json.loads(args.receipt.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(json.dumps({"passed": False, "errors": [str(exc)]}, indent=2))
        return 2

    errors = validate(data)
    result = {
        "passed": not errors,
        "commit_sha": data.get("theory", {}).get("commit_sha") if isinstance(data.get("theory"), dict) else None,
        "errors": errors,
    }
    rendered = json.dumps(result, indent=2, sort_keys=True)
    print(rendered)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    return 0 if not errors else 1


if __name__ == "__main__":
    sys.exit(main())
