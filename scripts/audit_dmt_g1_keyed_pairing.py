#!/usr/bin/env python3
"""Niedernhuber G1: provenance-keyed paired-observation audit.

Original source owners: Niedernhuber et al. 2026 DMT/harmine experiment;
Tait and Zhang +microstate stats_markov.m (G1); original analysis R/MATLAB.
Inspired by the existing DASHI order-erasure and source-conditioned evidence
machinery (including ongoing PRs #1255/#1259/#1240); no code imported from
unmerged PRs. This program does NOT reproduce the authors' ARTool ANOVA.

CRITICAL: source MATLAB Rprep first removes NaN rows JOINTLY across a
condition-column matrix, conditionally preserving positional alignment;
the later R reader removes missing entries per numeric file and reconstructs
Subject = 1..n. Source order and residual missingness still require a
participant-identity receipt before an independent pairing claim. We *require*
per-condition identity and effective sequence length at the individual row.
An external reviewer receipt is documentary, not independently checked rights.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

SCHEMA = "dashi-dmt-g1-source-keyed-v1"
RECEIPT_SCHEMA = "dashi-dmt-g1-reviewed-pairing-v1"
ARMS = ("DMT", "harmine", "placebo")
AUTHOR_CODE_COMMIT = "c5c064d109563e97127403a8fbb340009ba1e88b"
AUTHOR_G1_EXPORT_SHA = "3f58dde834189972410165cdd06392dea9220b33"
TOOLBOX_G1_SHA = "a738a95c4218b8de76920e8333cef307126ef13f"
ZENODO_VERSION = "10.5281/zenodo.18850897"
AUTHOR_IDS = tuple(("1001 1002 1003 1004 1006 1009 1010 1011 1013 1014 "
                    "1016 1019 1021 1022 1023 1024 1025 1026 1027 1028 "
                    "1029 1031 1038 1040 1041").split())
DOC_KEYS = {"schema", "mode", "dataset_id", "analysis_source_commit",
            "source_g1_export_blob", "source_toolbox_g1_blob",
            "source_version_doi", "condition_selection_provenance",
            "participant_crosswalk_provenance", "recording_length_provenance",
            "rows"}
ROW_KEYS = {"participant_id", "arm", "g1", "sample_count",
            "condition_session_reference", "g1_label_stream_reference",
            "label_sequence_type", "epoch_boundary_reference"}
REVIEW_KEYS = {"schema", "canonical_document_sha256", "reviewer_reference",
               "rights_permission_reference", "ethics_scope_reference",
               "condition_crosswalk_review_reference",
               "sequence_length_review_reference"}


def canonical_sha256(doc):
    return hashlib.sha256(json.dumps(doc, sort_keys=True, ensure_ascii=False,
                                     separators=(",", ":")).encode("utf8")).hexdigest()


def required_string(value, field):
    if not isinstance(value, str) or not value.strip() or value.strip().lower() in {
            "unknown", "tbd", "unverified", "none", "null"}:
        raise ValueError("Missing independently scoped reference: " + field)
    return value


def _parse_exact_g1(value):
    # Source MATLAB exports decimal numbers: require a quoted decimal or
    # fraction to avoid hidden binary-float changes to evidence.
    if not isinstance(value, str) or not value.strip():
        raise ValueError("G1 must be a nonnegative decimal string")
    try:
        number = Fraction(value)
    except (ValueError, ZeroDivisionError) as e:
        raise ValueError("Malformed/undefined G1") from e
    if number < 0:
        raise ValueError("Negative G1 not admitted by this finite estimator")
    return number


def validate(doc, receipt=None):
    if not isinstance(doc, dict) or set(doc) != DOC_KEYS or doc["schema"] != SCHEMA:
        raise ValueError("G1 keyed-observation contract mismatch")
    mode = doc["mode"]
    if mode not in ("synthetic", "reviewed_original_source"):
        raise ValueError("Only synthetic or separately reviewed original source permitted")
    ds = required_string(doc["dataset_id"], "dataset_id")
    for k in ("condition_selection_provenance", "participant_crosswalk_provenance",
              "recording_length_provenance"):
        required_string(doc[k], k)
    if (doc["analysis_source_commit"] != AUTHOR_CODE_COMMIT or
            doc["source_g1_export_blob"] != AUTHOR_G1_EXPORT_SHA or
            doc["source_toolbox_g1_blob"] != TOOLBOX_G1_SHA or
            doc["source_version_doi"] != ZENODO_VERSION):
        raise ValueError("Original source identifiers do not match provenance roots")
    if mode == "synthetic":
        if not ds.startswith("synthetic:") or receipt is not None:
            raise ValueError("Synthetic observations cannot claim rights/real-world authority")
    else:
        if ds.startswith("synthetic:") or not isinstance(receipt, dict) or set(receipt) != REVIEW_KEYS:
            raise ValueError("Independent real-data reviewer receipt required")
        if receipt["schema"] != RECEIPT_SCHEMA or receipt["canonical_document_sha256"] != canonical_sha256(doc):
            raise ValueError("Review receipt not bound to this exact canonical document")
        for k in REVIEW_KEYS - {"schema", "canonical_document_sha256"}:
            required_string(receipt[k], k)
    rows = doc["rows"]
    if not isinstance(rows, list) or not rows:
        raise ValueError("No keyed observations")
    pairs = {}
    sequence_types = set()
    for row in rows:
        if not isinstance(row, dict) or set(row) != ROW_KEYS:
            raise ValueError("Each row must have exact observed identity/provenance fields")
        pid = required_string(row["participant_id"], "participant_id")
        arm = row["arm"]
        if arm not in ARMS:
            raise ValueError("Unrecognized experimental arm")
        if mode != "synthetic" and pid not in AUTHOR_IDS:
            raise ValueError("Participant ID not in authors' pinned 25-ID roster")
        key = (pid, arm)
        if key in pairs:
            raise ValueError("Duplicate person-condition observation")
        n = row["sample_count"]
        if type(n) is not int or n < 3:
            raise ValueError("Need source-aligned contiguous G1 label sample count >=3")
        required_string(row["condition_session_reference"], "condition_session_reference")
        required_string(row["g1_label_stream_reference"], "g1_label_stream_reference")
        required_string(row["epoch_boundary_reference"], "epoch_boundary_reference")
        if row["label_sequence_type"] not in ("samplewise", "jump_collapsed"):
            raise ValueError("Original labelled sequence type must be source-specified")
        sequence_types.add(row["label_sequence_type"])
        g1 = _parse_exact_g1(row["g1"])
        pairs[key] = (g1, n)
    if len(sequence_types) != 1:
        raise ValueError("Mixed samplewise/jump G1 statistics are not the same comparison")
    persons = sorted({p for p, _ in pairs})
    if len(persons) < 2:
        raise ValueError("At least two independently keyed participants required")
    if mode != "synthetic" and set(persons) != set(AUTHOR_IDS):
        raise ValueError("Original 25-person reproduction requires all source IDs or an explicit amended eligibility contract")
    if len(pairs) != 3 * len(persons):
        raise ValueError("Missing condition per person; positional or complete-case silent join forbidden")
    if any((pid, arm) not in pairs for pid in persons for arm in ARMS):
        raise ValueError("Unmatched treatment arm")
    return persons, pairs, mode, next(iter(sequence_types))


def _summary(values):
    n = len(values)
    mu = sum(values, Fraction(0)) / n
    variance = sum(((x-mu)**2 for x in values), Fraction(0)) / (n-1)
    return {"n_participants": n, "mean_exact": str(mu),
            "sample_variance_exact": str(variance)}


def audit(doc, receipt=None):
    people, pairs, mode, sequence_type = validate(doc, receipt)
    result = {}
    for target in ("harmine", "placebo"):
        raw = [pairs[pid, "DMT"][0] - pairs[pid, target][0] for pid in people]
        normalized = [(pairs[pid, "DMT"][0] / (2*(pairs[pid, "DMT"][1]-2))
                       - pairs[pid, target][0] / (2*(pairs[pid, target][1]-2)))
                      for pid in people]
        result["DMT_vs_"+target] = {
            "G1_raw": _summary(raw),
            "conditional_information_per_triple_nats": _summary(normalized)}
    lengths = {pid: {arm: pairs[pid,arm][1] for arm in ARMS} for pid in people}
    length_equal = all(len(set(lens.values())) == 1 for lens in lengths.values())
    return {"schema": "dashi-dmt-g1-keyed-comparison-v1",
            "status": "synthetic_diagnostic" if mode == "synthetic" else
                      "reviewed_metadata_assertions_not_independent_rights_proof",
            "participants": len(people), "conditions": list(ARMS),
            "label_sequence_type": sequence_type,
            "mixed_sequence_types_rejected": True,
            "same_person_recording_lengths_equal_across_arms": length_equal,
            "contrasts": result,
            "direct_author_ARTool_ANOVA_reproduced": False,
            "original_experiment_reproduced": False,
            "source_permissions_independently_verified": False,
            "external_agent_ontology_established": False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("keyed_g1_json", type=Path)
    p.add_argument("--reviewer-receipt", type=Path)
    args = p.parse_args()
    data = json.loads(args.keyed_g1_json.read_text(encoding="utf8"))
    receipt = (json.loads(args.reviewer_receipt.read_text(encoding="utf8"))
               if args.reviewer_receipt else None)
    print(json.dumps(audit(data, receipt), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
