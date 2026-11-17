#!/usr/bin/env python3
"""Pre-registered-category temporal motif diagnostic; never an ontology test.

Only coded ordinal events are accepted, not raw experience-report text. Erowid
report use needs written rights-holder permission including applicable AI use.
Default execution is synthetic; a real-data run requires a separate, exact-byte
canonical-content-SHA256-bound reviewer receipt. Such a receipt is an admission control, not a
machine-verifiable legal determination or evidence of independent entities.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

SCHEMA = "dashi-dmt-temporal-motifs-v2"
RECEIPT_SCHEMA = "dashi-dmt-reviewed-source-admission-v1"
TOP_KEYS = {"schema", "mode", "observation_unit", "source_collection_id",
            "motif_vocabulary", "governance", "reports"}
REPORT_KEYS = {"report_id", "independence_unit_id", "source_collection_id",
               "chronology_verified", "events"}
EVENT_KEYS = {"ordinal", "motif"}
GOVERNANCE_KEYS = {"codebook_reference", "chronology_method_reference",
                   "source_identity_reference", "independence_review_reference"}


def canonical_sha256(document):
    return hashlib.sha256(json.dumps(document, sort_keys=True, separators=(",", ":"),
                                     ensure_ascii=False).encode("utf8")).hexdigest()


def _required_reference(item, name):
    value = item.get(name)
    if not isinstance(value, str) or not value.strip() or value.strip().lower() in {
        "unknown", "unverified", "none", "tbd", "synthetic-fixture-only"}:
        raise ValueError("Missing source/protocol provenance: " + name)
    return value


def _known_keys(item, keys, label):
    if not isinstance(item, dict) or set(item) != keys:
        raise ValueError(label + " must have exact declared fields (no raw text or PII)")


def _admit(data, approval_receipt):
    if data["mode"] == "synthetic":
        if approval_receipt is not None:
            raise ValueError("Synthetic data cannot claim research-data permission")
        if not data["source_collection_id"].startswith("synthetic:"):
            raise ValueError("Synthetic fixture source namespace required")
        return "synthetic_construction_only"
    if data["mode"] != "authorized_research":
        raise ValueError("Unrecognized corpus mode")
    if data["source_collection_id"].startswith("synthetic:"):
        raise ValueError("Synthetic collection cannot be relabeled as real research")
    if not isinstance(approval_receipt, dict) or set(approval_receipt) != {
        "schema", "dataset_sha256", "source_collection_id", "rights_holder",
        "permission_document_sha256", "reviewer_reference", "scope_reference",
        "ai_processing_in_scope", "temporal_analysis_in_scope"}:
        raise ValueError("Independent research-admission receipt required")
    if approval_receipt["schema"] != RECEIPT_SCHEMA:
        raise ValueError("Wrong source-admission receipt schema")
    if approval_receipt["dataset_sha256"] != canonical_sha256(data):
        raise ValueError("Approval receipt does not bind exact dataset")
    if approval_receipt["source_collection_id"] != data["source_collection_id"]:
        raise ValueError("Approval receipt names another source")
    for key in ("rights_holder", "permission_document_sha256", "reviewer_reference", "scope_reference"):
        _required_reference(approval_receipt, key)
    if len(approval_receipt["permission_document_sha256"]) != 64 or any(
            ch not in "0123456789abcdef" for ch in approval_receipt["permission_document_sha256"]):
        raise ValueError("Invalid written-permission document digest")
    if (approval_receipt["ai_processing_in_scope"] is not True or
            approval_receipt["temporal_analysis_in_scope"] is not True):
        raise ValueError("Permission scope does not cover analysis and AI processing")
    return "separate_reviewer_attestation_required_external_verification"


def validate(data, approval_receipt=None):
    _known_keys(data, TOP_KEYS, "Study")
    if data["schema"] != SCHEMA or data["observation_unit"] != "report":
        raise ValueError("Requires source-typed report-level observation schema v2")
    source = _required_reference(data, "source_collection_id")
    vocabulary = data["motif_vocabulary"]
    if (not isinstance(vocabulary, list) or len(vocabulary) < 2 or
            not all(isinstance(x, str) and x.strip() for x in vocabulary) or
            len(vocabulary) != len(set(vocabulary))):
        raise ValueError("Predeclared distinct motif vocabulary required")
    gov = data["governance"]
    _known_keys(gov, GOVERNANCE_KEYS, "Governance")
    for field in GOVERNANCE_KEYS:
        _required_reference(gov, field)
    reports = data["reports"]
    if not isinstance(reports, list) or len(reports) < 2:
        raise ValueError("At least two source-typed reports required")
    seen = set()
    groups = set()
    for r in reports:
        _known_keys(r, REPORT_KEYS, "Report")
        rid = _required_reference(r, "report_id")
        group = _required_reference(r, "independence_unit_id")
        if rid in seen:
            raise ValueError("Duplicate report ID")
        seen.add(rid)
        groups.add(group)
        if r["source_collection_id"] != source:
            raise ValueError("Cross-source pooling is not an admitted same-object join")
        if r["chronology_verified"] is not True:
            raise ValueError("Report chronology was not independently verified")
        events = r["events"]
        if not isinstance(events, list) or len(events) < 2:
            raise ValueError("At least two ordinal events per report required")
        indices = []
        for e in events:
            _known_keys(e, EVENT_KEYS, "Event")
            if type(e["ordinal"]) is not int or e["ordinal"] < 0 or e["motif"] not in vocabulary:
                raise ValueError("Ordinal or motif outside predeclared codebook")
            indices.append(e["ordinal"])
        if indices != sorted(set(indices)):
            raise ValueError("Positions must be strictly increasing and unique")
    if len(groups) < 2:
        raise ValueError("Two independent held-out groups required")
    status = _admit(data, approval_receipt)
    return reports, sorted(groups), vocabulary, status


def transitions(report):
    motifs = [e["motif"] for e in report["events"]]
    return list(zip(motifs, motifs[1:]))


def evaluate(data, approval_receipt=None):
    reports, groups, labels, admission = validate(data, approval_receipt)
    folds = []
    for held_group in groups:
        train = [r for r in reports if r["independence_unit_id"] != held_group]
        held = [r for r in reports if r["independence_unit_id"] == held_group]
        edges = Counter(edge for r in train for edge in transitions(r))
        origin = Counter()
        destination = Counter()
        for (a, b), n in edges.items():
            origin[a] += n
            destination[b] += n
        n_transitions = sum(destination.values())
        k = len(labels)
        temporal_likelihood = Fraction(1)
        static_likelihood = Fraction(1)
        held_n = 0
        for r in held:
            for a, b in transitions(r):
                temporal_likelihood *= Fraction(edges[a, b] + 1, origin[a] + k)
                static_likelihood *= Fraction(destination[b] + 1, n_transitions + k)
                held_n += 1
        folds.append({"held_out_independence_unit_id": held_group,
                      "held_out_report_count": len(held),
                      "held_out_transitions": held_n,
                      "temporal_probability_exact": str(temporal_likelihood),
                      "static_probability_exact": str(static_likelihood),
                      "temporal_vs_static_ratio_exact": str(temporal_likelihood / static_likelihood)})
    return {"schema": "dashi-dmt-temporal-motif-evaluation-v2",
            "admission_status": admission,
            "method": "leave-one-independence-unit-out / predeclared vocabulary / additive-one smoothing",
            "source_collection_id": data["source_collection_id"],
            "report_count": len(reports), "independence_units": len(groups),
            "motif_count": len(labels), "folds": folds,
            "held_out_predictive_comparison_only": True,
            "no_group_folds_treated_as_independent_pvalues": True,
            "permission_legality_not_automatically_established": True,
            "measured_neural_mechanism": False,
            "independent_external_agent_inferred": False,
            "same_participant_cross_study_join": False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("source_json", type=Path)
    p.add_argument("--reviewed-admission-receipt", type=Path)
    a = p.parse_args()
    data = json.loads(a.source_json.read_text(encoding="utf8"))
    receipt = (json.loads(a.reviewed_admission_receipt.read_text(encoding="utf8"))
               if a.reviewed_admission_receipt else None)
    print(json.dumps(evaluate(data, receipt), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
