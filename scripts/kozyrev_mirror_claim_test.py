#!/usr/bin/env python3
"""Fail-closed Kozyrev-mirror preregistration and paired sham analysis.

This is a computational assay, not evidence that a physical or clinical
effect exists. An outside timestamped registration and independent data
provenance audit remain mandatory. Uses only the Python standard library.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import math
from pathlib import Path

CLAIM_IDS = {
    "KM-SCATTER", "KM-SUBJECTIVE", "KM-CLINICAL",
    "KM-REMOTE", "KM-TIME",
}
REQUIRED = {
    "study_id", "claim_id", "source_uri", "primary_outcome", "outcome_unit",
    "n_pairs", "direction", "minimum_effect", "alpha",
    "preregistration_uri", "preregistration_timestamp_utc",
    "randomization_method", "blinding_policy", "sham_description",
    "calibration_reference", "negative_controls", "confound_controls",
    "analysis_plan", "safety_approval_status", "independent_replication_plan",
}


class InvalidEvidence(ValueError):
    pass


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_manifest(path: Path) -> dict:
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (ValueError, OSError) as exc:
        raise InvalidEvidence(f"cannot read preregistration manifest: {exc}") from exc
    if not isinstance(manifest, dict):
        raise InvalidEvidence("manifest must be a JSON object")
    absent = sorted(REQUIRED - manifest.keys())
    if absent:
        raise InvalidEvidence(f"missing required fields: {', '.join(absent)}")
    for key in REQUIRED - {"negative_controls", "confound_controls",
                            "n_pairs", "minimum_effect", "alpha"}:
        if not isinstance(manifest[key], str) or not manifest[key].strip():
            raise InvalidEvidence(f"{key} must be a nonempty string")
    for key in ("negative_controls", "confound_controls"):
        if (not isinstance(manifest[key], list)
                or len(manifest[key]) < 2
                or any(not isinstance(x, str) or not x.strip()
                       for x in manifest[key])):
            raise InvalidEvidence(f"{key} must name at least two distinct controls")
        if len(set(manifest[key])) != len(manifest[key]):
            raise InvalidEvidence(f"{key} repeats a control")
    if manifest["claim_id"] not in CLAIM_IDS:
        raise InvalidEvidence("claim is not an operationalised registry target")
    if type(manifest["n_pairs"]) is not int or not (2 <= manifest["n_pairs"] <= 18):
        raise InvalidEvidence("exact paired sign-flip assay requires 2-18 pairs")
    if manifest["direction"] not in ("positive", "negative", "two-sided"):
        raise InvalidEvidence("direction must be positive, negative, or two-sided")
    for key in ("alpha", "minimum_effect"):
        if isinstance(manifest[key], bool) or not isinstance(manifest[key], (float, int)):
            raise InvalidEvidence(f"{key} must be numeric")
        if not math.isfinite(manifest[key]):
            raise InvalidEvidence(f"{key} must be finite")
    if not (0 < manifest["alpha"] <= 0.05):
        raise InvalidEvidence("alpha must be fixed within (0, 0.05]")
    if manifest["minimum_effect"] < 0:
        raise InvalidEvidence("minimum_effect must be nonnegative")
    if not manifest["preregistration_timestamp_utc"].endswith("Z"):
        raise InvalidEvidence("preregistration timestamp must be in UTC")
    if manifest["claim_id"] in ("KM-SUBJECTIVE", "KM-CLINICAL"):
        if manifest["safety_approval_status"] != "approved":
            raise InvalidEvidence("human-subject analyses require recorded safety approval")
    return manifest


def paired_differences(path: Path, expected_pairs: int) -> list[float]:
    try:
        with path.open(encoding="utf-8", newline="") as handle:
            reader = csv.DictReader(handle)
            if reader.fieldnames is None or set(reader.fieldnames) != {
                "pair_id", "condition", "outcome"
            }:
                raise InvalidEvidence("CSV columns must be pair_id,condition,outcome")
            pairs: dict[str, dict[str, float]] = {}
            for row in reader:
                ident = row["pair_id"]
                arm = row["condition"]
                if not ident or arm not in ("active", "sham"):
                    raise InvalidEvidence("pair_id or condition invalid")
                try:
                    value = float(row["outcome"])
                except (TypeError, ValueError) as exc:
                    raise InvalidEvidence("outcome is not numeric") from exc
                if not math.isfinite(value):
                    raise InvalidEvidence("outcome must be finite")
                block = pairs.setdefault(ident, {})
                if arm in block:
                    raise InvalidEvidence("duplicate arm within a pair")
                block[arm] = value
    except OSError as exc:
        raise InvalidEvidence(f"cannot read observations: {exc}") from exc
    if len(pairs) != expected_pairs:
        raise InvalidEvidence("pair count differs from registered plan")
    if any(set(pair) != {"active", "sham"} for pair in pairs.values()):
        raise InvalidEvidence("each pair must contain one active and one sham")
    return [v["active"] - v["sham"] for _, v in sorted(pairs.items())]


def exact_sign_flip(differences: list[float], direction: str) -> float:
    """Exact conditional sign-flip randomization reference distribution.

    Its validity depends on a truly paired randomized design and exchangeable
    sign assignments under the sharp null; it cannot establish those facts.
    """
    n = len(differences)
    if not (2 <= n <= 18):
        raise InvalidEvidence("unsupported pair count")
    observed = sum(differences)
    tolerance = 1e-12 * max(1.0, sum(abs(x) for x in differences))
    extremes = 0
    for signs in itertools.product((-1, 1), repeat=n):
        total = sum(sign * value for sign, value in zip(signs, differences))
        if direction == "two-sided":
            reject = abs(total) + tolerance >= abs(observed)
        elif direction == "positive":
            reject = total + tolerance >= observed
        else:
            reject = total - tolerance <= observed
        extremes += bool(reject)
    return extremes / (1 << n)


def analyze(manifest: dict, data: Path) -> dict:
    differences = paired_differences(data, manifest["n_pairs"])
    effect = sum(differences) / len(differences)
    p = exact_sign_flip(differences, manifest["direction"])
    direction = manifest["direction"]
    magnitude = manifest["minimum_effect"]
    meets_effect = (
        effect >= magnitude if direction == "positive"
        else effect <= -magnitude if direction == "negative"
        else abs(effect) >= magnitude
    )
    candidate = p <= manifest["alpha"] and meets_effect
    return {
        "study_id": manifest["study_id"],
        "claim_id": manifest["claim_id"],
        "primary_outcome": manifest["primary_outcome"],
        "outcome_unit": manifest["outcome_unit"],
        "n_pairs": manifest["n_pairs"],
        "paired_active_minus_sham_mean": effect,
        "exact_sign_flip_p": p,
        "preregistered_minimum_effect": magnitude,
        "preregistered_alpha": manifest["alpha"],
        "signal_status": ("candidate_statistical_signal_requires_audit"
                          if candidate else "prespecified_gate_not_met"),
        "statistical_assumption": "paired randomized exchangeable signs under sharp null",
        "external_registration_verified": False,
        "calibration_and_negative_controls_verified": False,
        "independent_replication_verified": False,
        "physical_effect_established": False,
        "clinical_efficacy_established": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", required=True, type=Path)
    parser.add_argument("--data", type=Path)
    parser.add_argument("--frozen-plan-sha256")
    parser.add_argument("--frozen-data-sha256")
    args = parser.parse_args(argv)
    try:
        manifest = parse_manifest(args.plan)
        plan_hash = sha256(args.plan)
        report = {
            "manifest_schema": "kozyrev-mirror-claim-assay-v1",
            "manifest_sha256": plan_hash,
            "claim_id": manifest["claim_id"],
            "registered_plan_attestation_verified": False,
            "empirical_promotion": False,
            "clinical_promotion": False,
        }
        if args.data is not None:
            if not args.frozen_plan_sha256 or not args.frozen_data_sha256:
                raise InvalidEvidence(
                    "analysis requires both independently recorded frozen hashes"
                )
            data_hash = sha256(args.data)
            if plan_hash != args.frozen_plan_sha256:
                raise InvalidEvidence("manifest differs from frozen preregistration")
            if data_hash != args.frozen_data_sha256:
                raise InvalidEvidence("observations differ from frozen data hash")
            report["data_sha256"] = data_hash
            report.update(analyze(manifest, args.data))
        else:
            report["status"] = "schema_valid_not_executed"
        print(json.dumps(report, sort_keys=True, indent=2))
        return 0
    except InvalidEvidence as exc:
        print(json.dumps({"error": str(exc), "status": "rejected",
                          "empirical_promotion": False}, sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
