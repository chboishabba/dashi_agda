#!/usr/bin/env python3
"""Compile fail-closed adaptive Digital-ESD screening work products.

Consumes:
  * exact durable screening ledger produced by prepare_digital_esd_screening_ledger.py
  * exact deduplicated metadata universe

Produces advisory artifacts only:
  * candidate-assessments.jsonl
  * study-family-hypotheses.jsonl
  * calibration-queue.jsonl
  * pareto-review-queue.jsonl
  * fulltext-handoff-queue.jsonl
  * adaptive-screening-manifest.json

Authority boundary:
  candidate assessment / fibre / selector != screening decision.
Only explicit screening decision receipts remain authoritative.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import math
import re
from pathlib import Path
from typing import Any

import prepare_digital_esd_screening_ledger as base


def canonical_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_ref(prefix: str, payload: Any) -> str:
    return f"{prefix}:sha256:{sha256_bytes(canonical_bytes(payload))}"


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: row is not an object")
            rows.append(row)
    return rows


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> str:
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    return sha256_bytes(path.read_bytes())


def norm_text(value: str) -> str:
    value = value.casefold()
    value = re.sub(r"[^a-z0-9]+", " ", value)
    return " ".join(value.split())


def listish(value: Any) -> list[str]:
    if isinstance(value, list):
        return [str(x).strip() for x in value if str(x).strip()]
    if isinstance(value, str) and value.strip():
        return [value.strip()]
    return []


def assessment_for(receipt: dict[str, Any]) -> dict[str, Any]:
    snap = receipt.get("title_abstract_snapshot") or {}
    title = str(snap.get("title") or "")
    abstract = str(snap.get("abstract") or "")
    subject = " ".join(listish(snap.get("subject")))
    publication_type = " ".join(listish(snap.get("publication_type")))
    text = norm_text(" ".join([title, abstract, subject, publication_type]))

    feature = {
        "has_abstract": bool(abstract.strip()),
        "education_signal": any(x in text for x in ("education", "learning", "student", "teacher", "school", "university")),
        "digital_signal": any(x in text for x in ("digital", "technology", "online", "ict", "computer", "platform")),
        "sustainability_signal": any(x in text for x in ("sustainab", "environment", "climate", "circular", "green", "ecolog")),
        "empirical_signal": any(x in text for x in ("study", "survey", "experiment", "interview", "participants", "sample", "trial", "case study")),
        "review_signal": any(x in text for x in ("systematic review", "literature review", "scoping review", "meta analysis")),
    }

    positives = sum(
        int(feature[k])
        for k in ("education_signal", "digital_signal", "sustainability_signal")
    )
    if not feature["has_abstract"]:
        candidate = "unresolved"
        confidence = 0
        reasons = ["inaccessibleAbstract"]
    elif positives == 3 and (feature["empirical_signal"] or feature["review_signal"]):
        candidate = "include"
        confidence = 90
        reasons = ["potentiallyRelevant"]
    elif positives >= 2:
        candidate = "probable"
        confidence = 65
        reasons = ["requiresFullText"]
    elif positives == 0:
        candidate = "exclude"
        confidence = 70
        reasons = ["otherScreeningReason"]
    else:
        candidate = "unresolved"
        confidence = 35
        reasons = ["insufficientTitleAbstractEvidence"]

    payload = {
        "source_identity_reference": receipt["source_identity_reference"],
        "metadata_revision_reference": receipt["metadata_revision_reference"],
        "title_abstract_snapshot_reference": receipt["title_abstract_snapshot_reference"],
        "rubric_version": receipt["screening_rubric_version"],
        "candidate_decision": candidate,
        "confidence": confidence,
        "margin": abs(confidence - 50),
        "reason_code_candidates": reasons,
        "model_reference": "deterministic-rubric-features:v1",
        "feature_evidence": feature,
        "candidate_only": True,
        "creates_screening_decision": False,
        "creates_source_truth": False,
    }
    payload["assessment_reference"] = stable_ref("screening-candidate-assessment", payload)
    return payload


def metadata_index(metadata_path: Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in base.load_records(metadata_path):
        ref = base.source_identity(row)
        if ref in out:
            raise ValueError(f"duplicate source identity in exact metadata universe: {ref}")
        out[ref] = row
    return out


def fibre_hypotheses(metadata: dict[str, dict[str, Any]]) -> tuple[list[dict[str, Any]], dict[str, int]]:
    groups: dict[tuple[str, str], list[str]] = collections.defaultdict(list)
    for ref, row in metadata.items():
        doi = base.first_text(row, "DOI", "doi").casefold().strip()
        title = norm_text(base.first_text(row, "Title", "title"))
        author = norm_text(base.first_text(row, "Author", "Authors", "author", "authors"))
        year = norm_text(base.first_text(row, "PublicationDate", "publication_date", "Year", "year"))

        if doi:
            groups[("publicationDuplicate", f"doi:{doi}")].append(ref)
        if title:
            groups[("reportFamilyDuplicate", f"title:{title}")].append(ref)
        if title and author and year:
            groups[("sameEmpiricalStudy", f"title-author-year:{title}|{author}|{year}")].append(ref)

    rows: list[dict[str, Any]] = []
    payoff: dict[str, int] = collections.Counter()
    for (kind, evidence_key), members in sorted(groups.items()):
        unique = sorted(set(members))
        if len(unique) < 2:
            continue
        payload = {
            "relation_kind": kind,
            "member_source_references": unique,
            "evidence_reference": evidence_key,
            "reviewed_as_same_object": False,
            "hypothesis_creates_empirical_study_identity": False,
            "candidate_only": True,
        }
        payload["fibre_reference"] = stable_ref("screening-fibre-hypothesis", payload)
        rows.append(payload)
        for member in unique:
            payoff[member] = max(payoff[member], len(unique) - 1)
    return rows, dict(payoff)


def stratum(assessment: dict[str, Any], duplicate_payoff: int, receipt: dict[str, Any]) -> str:
    snap = receipt.get("title_abstract_snapshot") or {}
    if not str(snap.get("abstract") or "").strip():
        return "missingAbstractOrMalformedMetadata"
    if duplicate_payoff > 0:
        return "duplicateAmbiguity"
    decision = assessment["candidate_decision"]
    confidence = int(assessment["confidence"])
    if confidence <= 45:
        return "highUncertainty"
    if decision in {"include", "probable"} and confidence >= 65:
        return "obviousRetainedCandidate"
    if decision == "exclude" and confidence >= 65:
        return "obviousExclusionCandidate"
    return "rareTerminologyOrSourceType"


def pareto_front(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    def dominates(a: dict[str, Any], b: dict[str, Any]) -> bool:
        am = a["axes"]
        bm = b["axes"]
        max_keys = ("boundary_information_gain", "likely_corpus_contraction", "rare_cell_coverage", "duplicate_family_payoff")
        weak = all(am[k] >= bm[k] for k in max_keys) and am["reviewer_cost"] <= bm["reviewer_cost"]
        strict = any(am[k] > bm[k] for k in max_keys) or am["reviewer_cost"] < bm["reviewer_cost"]
        return weak and strict

    return [
        row for i, row in enumerate(rows)
        if not any(i != j and dominates(other, row) for j, other in enumerate(rows))
    ]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", required=True, type=Path)
    ap.add_argument("--metadata-input", required=True, type=Path)
    ap.add_argument("--out-dir", type=Path, default=Path("artifacts/digital-esd/adaptive-screening"))
    ap.add_argument("--review-budget", type=int, default=500)
    args = ap.parse_args()

    ledger = load_jsonl(args.ledger)
    metadata = metadata_index(args.metadata_input)
    by_ref = {r["source_identity_reference"]: r for r in ledger}
    if set(by_ref) != set(metadata):
        missing_from_ledger = sorted(set(metadata) - set(by_ref))
        missing_from_metadata = sorted(set(by_ref) - set(metadata))
        raise RuntimeError(
            "denominator mismatch between exact metadata universe and screening ledger; "
            f"missing_from_ledger={missing_from_ledger[:10]} "
            f"missing_from_metadata={missing_from_metadata[:10]}"
        )

    args.out_dir.mkdir(parents=True, exist_ok=True)

    assessments = [assessment_for(by_ref[ref]) for ref in sorted(by_ref)]
    assess_by_ref = {r["source_identity_reference"]: r for r in assessments}
    fibres, payoff = fibre_hypotheses(metadata)

    unresolved_refs = sorted(
        ref for ref, receipt in by_ref.items() if receipt.get("decision") == "unresolved"
    )
    strata_counts: collections.Counter[str] = collections.Counter()
    candidates: list[dict[str, Any]] = []

    pub_type_frequency: collections.Counter[str] = collections.Counter()
    for ref in unresolved_refs:
        snap = by_ref[ref].get("title_abstract_snapshot") or {}
        ptype = norm_text(" ".join(listish(snap.get("publication_type")))) or "<missing>"
        pub_type_frequency[ptype] += 1

    for ref in unresolved_refs:
        receipt = by_ref[ref]
        assessment = assess_by_ref[ref]
        s = stratum(assessment, payoff.get(ref, 0), receipt)
        strata_counts[s] += 1
        snap = receipt.get("title_abstract_snapshot") or {}
        ptype = norm_text(" ".join(listish(snap.get("publication_type")))) or "<missing>"
        abstract_len = len(str(snap.get("abstract") or ""))
        info_gain = 100 - int(assessment["margin"])
        contraction = int(assessment["confidence"])
        rare = max(0, 100 - min(100, pub_type_frequency[ptype]))
        duplicate = min(100, payoff.get(ref, 0) * 20)
        reviewer_cost = max(1, min(100, math.ceil(abstract_len / 100)))
        candidates.append({
            "source_identity_reference": ref,
            "assessment_reference": assessment["assessment_reference"],
            "stratum": s,
            "axes": {
                "boundary_information_gain": info_gain,
                "likely_corpus_contraction": contraction,
                "rare_cell_coverage": rare,
                "duplicate_family_payoff": duplicate,
                "reviewer_cost": reviewer_cost,
            },
            "selection_creates_screening_decision": False,
            "candidate_only": True,
        })

    front = pareto_front(candidates)
    front_refs = {r["source_identity_reference"] for r in front}
    ranked = sorted(
        candidates,
        key=lambda r: (
            r["source_identity_reference"] not in front_refs,
            -(r["axes"]["boundary_information_gain"]
              + r["axes"]["likely_corpus_contraction"]
              + r["axes"]["rare_cell_coverage"]
              + r["axes"]["duplicate_family_payoff"]
              - r["axes"]["reviewer_cost"]),
            r["source_identity_reference"],
        ),
    )
    selected = ranked[: max(0, args.review_budget)]

    calibration_queue: list[dict[str, Any]] = []
    per_stratum = max(1, args.review_budget // max(1, len(strata_counts)))
    for s in sorted(strata_counts):
        rows = [r for r in ranked if r["stratum"] == s][:per_stratum]
        for row in rows:
            calibration_queue.append({
                **row,
                "calibration_round_reference": "digital-esd-screening-calibration:v1",
                "review_required": True,
                "automatic_decision_authority": False,
            })

    retained = [
        {
            "source_identity_reference": ref,
            "screening_decision_reference": receipt["decision_reference"],
            "decision": receipt["decision"],
            "full_text_acquisition_required": True,
            "same_object_identity_review_required": True,
            "canonical_slr_evidence_required": True,
            "reviewed_slr_evidence_required": True,
            "digital_esd_audit_projection_required": True,
            "source_audit_admission_required": True,
            "screening_alone_creates_audit_admission": False,
            "slr_alone_creates_audit_admission": False,
        }
        for ref, receipt in sorted(by_ref.items())
        if receipt.get("decision") in {"include", "probable"}
    ]

    counts = collections.Counter(str(r.get("decision")) for r in ledger)
    n0 = len(ledger)
    reviewed = n0 - counts["unresolved"]
    denominator = {
        "schema": "digital-esd-screening-denominator-integrity-v1",
        "n0_exact_universe": n0,
        "n_reviewed": reviewed,
        "n_still_unreviewed": counts["unresolved"],
        "n_include": counts["include"],
        "n_probable": counts["probable"],
        "n_exclude": counts["exclude"],
        "n_unresolved": counts["unresolved"],
        "n_report_family_hypotheses": len(fibres),
        "n_full_text_sought_queue": len(retained),
        "n0_equals_reviewed_plus_unreviewed": n0 == reviewed + counts["unresolved"],
        "every_unselected_record_remains_in_ledger": True,
        "unresolved_is_not_exclusion": True,
    }

    artifacts = {}
    for name, rows in [
        ("candidate-assessments.jsonl", assessments),
        ("study-family-hypotheses.jsonl", fibres),
        ("calibration-queue.jsonl", calibration_queue),
        ("pareto-review-queue.jsonl", selected),
        ("fulltext-handoff-queue.jsonl", retained),
    ]:
        path = args.out_dir / name
        artifacts[name] = {"sha256": write_jsonl(path, rows), "rows": len(rows)}

    denominator_path = args.out_dir / "screening-denominator.json"
    denominator_path.write_text(json.dumps(denominator, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    artifacts[denominator_path.name] = {"sha256": sha256_bytes(denominator_path.read_bytes()), "rows": 1}

    manifest = {
        "schema": "digital-esd-adaptive-screening-controller-v1",
        "screening_ledger_reference": str(args.ledger),
        "screening_ledger_sha256": sha256_bytes(args.ledger.read_bytes()),
        "metadata_universe_reference": str(args.metadata_input),
        "metadata_universe_sha256": sha256_bytes(args.metadata_input.read_bytes()),
        "review_budget": args.review_budget,
        "pareto_front_size": len(front),
        "strata_counts": dict(sorted(strata_counts.items())),
        "artifacts": artifacts,
        "candidate_assessment_creates_screening_decision": False,
        "selector_creates_screening_decision": False,
        "fibre_hypothesis_creates_study_identity": False,
        "screening_alone_creates_audit_admission": False,
        "slr_alone_creates_audit_admission": False,
    }
    manifest["manifest_reference"] = stable_ref("adaptive-screening-manifest", manifest)
    manifest_path = args.out_dir / "adaptive-screening-manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "DIGITAL_ESD_ADAPTIVE_SCREENING "
        f"n0={n0} reviewed={reviewed} unresolved={counts['unresolved']} "
        f"fibres={len(fibres)} pareto_front={len(front)} selected={len(selected)} "
        f"fulltext_queue={len(retained)}"
    )
    print(f"manifest: {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
