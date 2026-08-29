#!/usr/bin/env python3
"""Validate external relation-representation study receipts.

This checker is intentionally stricter than a bibliography check.  A cited
paper or public code URL is not a reproduction receipt.  For a non-template
receipt, study-specific artifact classes, pinned model/code/environment
identity, payload locations, and content hashes must all be present.

The required artifact sets mirror the source-bounded method profiles in
DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCHEMA = "dashi.relation-representation.external-study-receipt.v1"

REQUIRED = {
    "christ-2510.26543": {
        "exactModelIdentity",
        "modelRevisionOrWeightHash",
        "tokenizerOrInputEncoding",
        "datasetIdentityAndVersion",
        "rawPairedExamples",
        "trainValidationTestSplit",
        "layerOrRepresentationLocation",
        "fittedOperatorParameters",
        "rawPredictionOrSimilarityScores",
        "parameterCountOrCompressionRatio",
        "randomSeedsAndEnvironment",
        "codeRevision",
    },
    "rise-2510.09790": {
        "exactModelIdentity",
        "modelRevisionOrWeightHash",
        "datasetIdentityAndVersion",
        "rawPairedExamples",
        "trainValidationTestSplit",
        "preprocessingReceipt",
        "rawEmbeddingsOrActivations",
        "fittedOperatorParameters",
        "baselineOperatorParameters",
        "rawPredictionOrSimilarityScores",
        "syntheticGenerationPromptAndModel",
        "deduplicationOrCollisionReceipt",
        "randomSeedsAndEnvironment",
        "codeRevision",
    },
    "recos-2602.05266": {
        "exactModelIdentity",
        "modelRevisionOrWeightHash",
        "datasetIdentityAndVersion",
        "rawPairedExamples",
        "preprocessingReceipt",
        "rawEmbeddingsOrActivations",
        "metricImplementation",
        "rawPredictionOrSimilarityScores",
        "groundTruthOrHumanJudgments",
        "statisticalTestReceipt",
        "randomSeedsAndEnvironment",
        "codeRevision",
    },
    "magnitude-2509.19323": {
        "exactModelIdentity",
        "modelRevisionOrWeightHash",
        "datasetIdentityAndVersion",
        "rawPairedExamples",
        "trainValidationTestSplit",
        "rawEmbeddingsOrActivations",
        "metricImplementation",
        "rawPredictionOrSimilarityScores",
        "groundTruthOrHumanJudgments",
        "statisticalTestReceipt",
        "randomSeedsAndEnvironment",
        "codeRevision",
    },
    "calibrated-2601.16907": {
        "exactModelIdentity",
        "modelRevisionOrWeightHash",
        "datasetIdentityAndVersion",
        "rawPairedExamples",
        "trainValidationTestSplit",
        "rawEmbeddingsOrActivations",
        "fittedOperatorParameters",
        "rawPredictionOrSimilarityScores",
        "groundTruthOrHumanJudgments",
        "statisticalTestReceipt",
        "randomSeedsAndEnvironment",
        "codeRevision",
    },
    "manifold-2605.05115": {
        "exactModelIdentity",
        "modelRevisionOrWeightHash",
        "datasetIdentityAndVersion",
        "rawPairedExamples",
        "trainValidationTestSplit",
        "layerOrRepresentationLocation",
        "rawEmbeddingsOrActivations",
        "fittedGeometryOrManifold",
        "fittedOperatorParameters",
        "baselineOperatorParameters",
        "interventionTrajectory",
        "outputDistributionTrajectory",
        "rawPredictionOrSimilarityScores",
        "randomSeedsAndEnvironment",
        "codeRevision",
    },
    "fde-2606.01402": {
        "exactModelIdentity",
        "modelRevisionOrWeightHash",
        "datasetIdentityAndVersion",
        "trainValidationTestSplit",
        "preprocessingReceipt",
        "fittedOperatorParameters",
        "compressionTolerance",
        "compressionPartition",
        "baselineOperatorParameters",
        "rawPredictionOrSimilarityScores",
        "parameterCountOrCompressionRatio",
        "randomSeedsAndEnvironment",
        "codeRevision",
    },
}


def nonempty(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def validate(path: Path, allow_template: bool) -> list[str]:
    data = json.loads(path.read_text(encoding="utf-8"))
    errors: list[str] = []

    if data.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA!r}")

    key = data.get("study_key")
    if key not in REQUIRED:
        errors.append(f"unknown study_key {key!r}; expected one of {sorted(REQUIRED)}")
        return errors

    status = data.get("status")
    is_template = status == "template"
    if is_template and allow_template:
        # A template is allowed to be incomplete, but it must still name its
        # source and must not masquerade as a reproduced/validated payload.
        source = data.get("source") or {}
        if not nonempty(source.get("authors")):
            errors.append("template source.authors must be present")
        if not nonempty(source.get("title")):
            errors.append("template source.title must be present")
        if not nonempty(source.get("identifier")):
            errors.append("template source.identifier must be present")
        if data.get("payloads") not in ([], None):
            errors.append("canonical template must not contain empirical payloads")
        return errors

    if status not in {"candidate", "checked-package", "reproduced"}:
        errors.append("status must be candidate, checked-package, or reproduced")

    for field in (
        "model_or_system_identity",
        "model_revision_or_weight_hash",
        "code_revision",
        "environment_digest",
    ):
        if not nonempty(data.get(field)):
            errors.append(f"missing non-empty {field}")

    payloads = data.get("payloads")
    if not isinstance(payloads, list):
        errors.append("payloads must be a list")
        return errors

    present: set[str] = set()
    for i, item in enumerate(payloads):
        if not isinstance(item, dict):
            errors.append(f"payloads[{i}] must be an object")
            continue
        artifact = item.get("artifact")
        if not nonempty(artifact):
            errors.append(f"payloads[{i}].artifact missing")
            continue
        present.add(artifact)
        for field in ("location", "content_hash", "producer_revision"):
            if not nonempty(item.get(field)):
                errors.append(f"payloads[{i}].{field} missing for {artifact}")

    missing = sorted(REQUIRED[key] - present)
    if missing:
        errors.append("missing required artifact classes: " + ", ".join(missing))

    # Even a complete package must not claim inferential promotions in the raw
    # receipt schema.  Those belong to Stage-6/7 owners after independent checks.
    forbidden_true = (
        "semantic_realization_established",
        "global_identifiability_established",
        "robust_model_adequacy_established",
        "normative_authority_established",
    )
    for field in forbidden_true:
        if data.get(field) is True:
            errors.append(f"raw receipt may not assert {field}=true")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--allow-template", action="store_true")
    args = parser.parse_args()

    errors = validate(args.receipt, args.allow_template)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    print(f"validated receipt package shape: {args.receipt}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
