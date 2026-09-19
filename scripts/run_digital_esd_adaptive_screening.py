#!/usr/bin/env python3
"""Fail-closed Digital-ESD P0-A -> P0-G adaptive screening controller.

This runtime never writes authoritative include/exclude screening decisions.
It consumes the durable screening ledger produced by
prepare_digital_esd_screening_ledger.py and emits lower-authority work products:

P0-A denominator receipt over the exact screening universe
P0-B candidate screening assessments
P0-C duplicate/report/study-family hypotheses
P0-D stratified calibration work queue
P0-E calibration diagnostics from explicit reviewed decisions
P0-F Pareto-ranked unresolved work queue
P0-G retained/probable full-text handoff manifest

Authority boundary:
  candidate assessment != screening decision
  selection/prioritisation != screening decision
  duplicate hypothesis != same empirical study
  screening decision != SourceAuditAdmission
  SLR review != SourceAuditAdmission
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

DECISIONS = {"include", "probable", "exclude", "unresolved"}
RETAINED = {"include", "probable"}
TOKEN_RE = re.compile(r"[a-z0-9]+")
STOP = {
    "a","an","and","are","as","at","be","by","for","from","in","is","it",
    "of","on","or","that","the","this","to","was","were","with",
}


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_ref(prefix: str, value: Any) -> str:
    return f"{prefix}:sha256:{sha256_bytes(canonical_bytes(value))}"


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    out = []
    with path.open("r", encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: row is not an object")
            out.append(row)
    return out


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def load_screening_ledger(path: Path) -> list[dict[str, Any]]:
    rows = read_jsonl(path)
    seen: set[str] = set()
    for i, row in enumerate(rows):
        src = str(row.get("source_identity_reference") or "").strip()
        decision = str(row.get("decision") or "").strip()
        if not src:
            raise ValueError(f"ledger row {i} missing source identity")
        if src in seen:
            raise ValueError(f"duplicate source identity in screening ledger: {src}")
        seen.add(src)
        if decision not in DECISIONS:
            raise ValueError(f"ledger row {src} has invalid decision {decision!r}")
        if row.get("decision_creates_source_truth") is not False:
            raise ValueError(f"{src}: screening truth firewall missing")
        if row.get("decision_creates_source_audit_admission") is not False:
            raise ValueError(f"{src}: screening admission firewall missing")
    return rows


def tokens(row: dict[str, Any]) -> set[str]:
    snap = row.get("title_abstract_snapshot") or {}
    text = " ".join(str(snap.get(k) or "") for k in ("title", "abstract"))
    return {x for x in TOKEN_RE.findall(text.lower()) if x not in STOP and len(x) > 2}


def normalised_title(row: dict[str, Any]) -> str:
    snap = row.get("title_abstract_snapshot") or {}
    title = str(snap.get("title") or "").lower()
    return " ".join(TOKEN_RE.findall(title))


def candidate_features(row: dict[str, Any]) -> dict[str, Any]:
    ts = tokens(row)
    snap = row.get("title_abstract_snapshot") or {}
    abstract = str(snap.get("abstract") or "")
    publication_type = snap.get("publication_type")
    subject = snap.get("subject")

    vocab = {
        "education": {"education","educational","student","students","teacher","teachers","learning","school","schools","university","universities","curriculum","pedagogy"},
        "digital": {"digital","technology","technologies","online","computer","computing","ict","ai","artificial","platform","virtual","elearning"},
        "sustainability": {"sustainability","sustainable","environment","environmental","climate","circularity","lifecycle","ecological","esd"},
        "empirical": {"study","survey","interview","participants","sample","experiment","trial","data","analysis","case","longitudinal","randomized","randomised"},
    }
    hits = {k: len(ts & v) for k, v in vocab.items()}
    missing_abstract = not abstract.strip()
    score = (
        1.0 * min(hits["education"], 2)
        + 1.0 * min(hits["digital"], 2)
        + 1.0 * min(hits["sustainability"], 2)
        + 0.5 * min(hits["empirical"], 2)
    )
    return {
        "token_count": len(ts),
        "education_hits": hits["education"],
        "digital_hits": hits["digital"],
        "sustainability_hits": hits["sustainability"],
        "empirical_hits": hits["empirical"],
        "missing_abstract": missing_abstract,
        "publication_type": publication_type,
        "subject_present": subject not in (None, "", []),
        "heuristic_relevance_score": score,
    }


def candidate_assessment(row: dict[str, Any], model_ref: str) -> dict[str, Any]:
    features = candidate_features(row)
    score = float(features["heuristic_relevance_score"])
    missing = bool(features["missing_abstract"])

    # Candidate-only suggestion. Never becomes a screening decision by this script.
    if missing:
        candidate = "unresolved"
        reason = ["inaccessibleAbstract", "insufficientTitleAbstractEvidence"]
        margin = 0.0
    elif score >= 4.0:
        candidate = "probable"
        reason = ["potentiallyRelevant", "requiresFullText"]
        margin = min(1.0, (score - 3.0) / 3.0)
    elif score <= 1.0:
        candidate = "exclude"
        reason = ["insufficientTitleAbstractEvidence"]
        margin = min(1.0, (2.0 - score) / 2.0)
    else:
        candidate = "unresolved"
        reason = ["awaitingScreeningReview"]
        margin = max(0.0, 1.0 - abs(score - 2.5) / 2.5)

    payload = {
        "source_identity_reference": row["source_identity_reference"],
        "metadata_revision_reference": row.get("metadata_revision_reference"),
        "title_abstract_snapshot_reference": row.get("title_abstract_snapshot_reference"),
        "rubric_version": row.get("screening_rubric_version"),
        "candidate_decision": candidate,
        "confidence_reference": f"heuristic-score:{score:.3f}",
        "margin_reference": f"heuristic-margin:{margin:.3f}",
        "reason_code_candidates": reason,
        "model_reference": model_ref,
        "feature_evidence": features,
        "candidate_only": True,
        "creates_screening_decision": False,
        "creates_source_truth": False,
    }
    payload["assessment_reference"] = stable_ref("screening-candidate-assessment", payload)
    return payload


def pair_similarity(a: dict[str, Any], b: dict[str, Any]) -> float:
    ta, tb = tokens(a), tokens(b)
    if not ta or not tb:
        return 0.0
    return len(ta & tb) / len(ta | tb)


def build_family_hypotheses(rows: list[dict[str, Any]], threshold: float) -> list[dict[str, Any]]:
    # Candidate fibres only. Block by normalised title prefix to stay bounded.
    blocks: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        title = normalised_title(row)
        key = " ".join(title.split()[:4])
        if key:
            blocks[key].append(row)

    out = []
    for key, members in sorted(blocks.items()):
        if len(members) < 2:
            continue
        # Limit quadratic comparison to title-prefix blocks.
        for i in range(len(members)):
            for j in range(i + 1, len(members)):
                a, b = members[i], members[j]
                sim = pair_similarity(a, b)
                if sim < threshold:
                    continue
                relation = "publicationDuplicate" if normalised_title(a) == normalised_title(b) else "reportFamilyDuplicate"
                payload = {
                    "fibre_reference": stable_ref("study-family-hypothesis", [a["source_identity_reference"], b["source_identity_reference"], relation]),
                    "member_source_references": [a["source_identity_reference"], b["source_identity_reference"]],
                    "relation_kind": relation,
                    "evidence_reference": f"title-abstract-jaccard:{sim:.6f}",
                    "reviewed_as_same_object": False,
                    "hypothesis_creates_empirical_study_identity": False,
                }
                out.append(payload)
    return out


def assessment_map(assessments: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    return {str(x["source_identity_reference"]): x for x in assessments}


def stratum(row: dict[str, Any], assessment: dict[str, Any], family_membership: set[str]) -> str:
    features = assessment["feature_evidence"]
    score = float(features["heuristic_relevance_score"])
    if features["missing_abstract"]:
        return "missingAbstractOrMalformedMetadata"
    if row["source_identity_reference"] in family_membership:
        return "duplicateAmbiguity"
    if score >= 4.5:
        return "obviousRetainedCandidate"
    if score <= 0.5:
        return "obviousExclusionCandidate"
    if score >= 1.5 and score <= 3.5:
        return "highUncertainty"
    return "rareTerminologyOrSourceType"


def calibration_queue(
    ledger: list[dict[str, Any]],
    assessments: list[dict[str, Any]],
    hypotheses: list[dict[str, Any]],
    per_stratum: int,
) -> list[dict[str, Any]]:
    amap = assessment_map(assessments)
    family_members = {m for h in hypotheses for m in h["member_source_references"]}
    buckets: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in ledger:
        if row["decision"] != "unresolved":
            continue
        a = amap[row["source_identity_reference"]]
        s = stratum(row, a, family_members)
        buckets[s].append({
            "source_identity_reference": row["source_identity_reference"],
            "stratum": s,
            "assessment_reference": a["assessment_reference"],
            "selection_creates_screening_decision": False,
        })

    out = []
    for s in [
        "obviousRetainedCandidate","obviousExclusionCandidate","highUncertainty",
        "duplicateAmbiguity","rareTerminologyOrSourceType","missingAbstractOrMalformedMetadata"
    ]:
        rows = sorted(buckets.get(s, []), key=lambda x: x["source_identity_reference"])
        out.extend(rows[:per_stratum])
    return out


def calibration_diagnostics(
    ledger: list[dict[str, Any]], assessments: list[dict[str, Any]]
) -> dict[str, Any]:
    amap = assessment_map(assessments)
    reviewed = [r for r in ledger if r["decision"] != "unresolved"]
    if not reviewed:
        return {
            "reviewed_count": 0,
            "false_negative_risk_reference": "unobserved:no-reviewed-calibration",
            "disagreement_structure": {},
            "rubric_ambiguity_reference": "unobserved:no-reviewed-calibration",
            "residual_classes": ["requiresReviewedCalibration"],
            "calibration_creates_automatic_decision_authority": False,
        }

    confusion = Counter()
    candidate_exclude_review_retained = 0
    unresolved_candidate = 0
    for row in reviewed:
        cand = amap[row["source_identity_reference"]]["candidate_decision"]
        actual = row["decision"]
        confusion[(cand, actual)] += 1
        if cand == "exclude" and actual in RETAINED:
            candidate_exclude_review_retained += 1
        if cand == "unresolved":
            unresolved_candidate += 1

    return {
        "reviewed_count": len(reviewed),
        "false_negative_risk_reference": f"candidate-exclude-reviewed-retained:{candidate_exclude_review_retained}/{len(reviewed)}",
        "disagreement_structure": {
            f"{a}->{b}": n for (a, b), n in sorted(confusion.items())
        },
        "rubric_ambiguity_reference": f"candidate-unresolved-among-reviewed:{unresolved_candidate}/{len(reviewed)}",
        "residual_classes": sorted({b for (a, b), n in confusion.items() if a != b and n}),
        "calibration_creates_automatic_decision_authority": False,
    }


def pareto_metrics(
    row: dict[str, Any],
    assessment: dict[str, Any],
    family_membership: set[str],
    rare_terms: set[str],
) -> dict[str, float]:
    f = assessment["feature_evidence"]
    score = float(f["heuristic_relevance_score"])
    # Information gain peaks near the heuristic boundary, not at extremes.
    information = 1.0 - min(1.0, abs(score - 2.5) / 2.5)
    contraction = min(1.0, abs(score - 2.5) / 2.5)
    rare = 1.0 if tokens(row) & rare_terms else 0.0
    duplicate = 1.0 if row["source_identity_reference"] in family_membership else 0.0
    reviewer_cost = 1.0 if f["missing_abstract"] else min(1.0, max(0.1, f["token_count"] / 400.0))
    return {
        "boundary_information_gain": information,
        "likely_corpus_contraction": contraction,
        "rare_cell_coverage": rare,
        "duplicate_family_payoff": duplicate,
        "reviewer_cost": reviewer_cost,
    }


def dominates(a: dict[str, float], b: dict[str, float]) -> bool:
    gain_keys = [
        "boundary_information_gain","likely_corpus_contraction",
        "rare_cell_coverage","duplicate_family_payoff"
    ]
    at_least = all(a[k] >= b[k] for k in gain_keys) and a["reviewer_cost"] <= b["reviewer_cost"]
    strict = any(a[k] > b[k] for k in gain_keys) or a["reviewer_cost"] < b["reviewer_cost"]
    return at_least and strict


def pareto_queue(
    ledger: list[dict[str, Any]],
    assessments: list[dict[str, Any]],
    hypotheses: list[dict[str, Any]],
    limit: int,
) -> list[dict[str, Any]]:
    amap = assessment_map(assessments)
    family_members = {m for h in hypotheses for m in h["member_source_references"]}

    freq = Counter()
    for row in ledger:
        freq.update(tokens(row))
    rare_terms = {term for term, n in freq.items() if 1 <= n <= 3}

    candidates = []
    for row in ledger:
        if row["decision"] != "unresolved":
            continue
        a = amap[row["source_identity_reference"]]
        metrics = pareto_metrics(row, a, family_members, rare_terms)
        candidates.append((row, a, metrics))

    front = []
    for i, item in enumerate(candidates):
        _, _, metrics = item
        if not any(dominates(other[2], metrics) for j, other in enumerate(candidates) if i != j):
            front.append(item)

    def utility(item: tuple[dict[str, Any], dict[str, Any], dict[str, float]]) -> tuple[float, str]:
        row, _, m = item
        score = (
            m["boundary_information_gain"]
            + m["likely_corpus_contraction"]
            + m["rare_cell_coverage"]
            + m["duplicate_family_payoff"]
            - m["reviewer_cost"]
        )
        return (-score, row["source_identity_reference"])

    selected = sorted(front, key=utility)[:limit]
    return [{
        "source_identity_reference": row["source_identity_reference"],
        "assessment_reference": a["assessment_reference"],
        "pareto_metrics": metrics,
        "pareto_front": True,
        "selection_creates_screening_decision": False,
        "unselected_records_remain_in_denominator": True,
    } for row, a, metrics in selected]


def denominator_receipt(ledger: list[dict[str, Any]], hypotheses: list[dict[str, Any]], fulltext: list[dict[str, Any]] | None) -> dict[str, Any]:
    counts = Counter(r["decision"] for r in ledger)
    reviewed = sum(counts[d] for d in ("include","probable","exclude"))
    still = counts["unresolved"]
    sought = obtained = unavailable = admitted = rejected_ft = 0
    if fulltext:
        sought = len(fulltext)
        obtained = sum(1 for r in fulltext if r.get("full_text_obtained") is True)
        unavailable = sum(1 for r in fulltext if r.get("full_text_unavailable") is True)
        admitted = sum(1 for r in fulltext if r.get("source_audit_admitted") is True)
        rejected_ft = sum(1 for r in fulltext if r.get("rejected_after_full_text") is True)
    return {
        "schema": "digital-esd-screening-denominator-integrity-v1",
        "n0": len(ledger),
        "reviewed": reviewed,
        "still_unreviewed": still,
        "include": counts["include"],
        "probable": counts["probable"],
        "exclude": counts["exclude"],
        "unresolved": counts["unresolved"],
        "report_family_hypotheses": len(hypotheses),
        "full_text_sought": sought,
        "full_text_obtained": obtained,
        "full_text_unavailable": unavailable,
        "audit_admitted": admitted,
        "rejected_after_full_text": rejected_ft,
        "n0_equals_reviewed_plus_unreviewed": len(ledger) == reviewed + still,
        "every_universe_member_retained": True,
        "unresolved_is_not_exclusion": True,
    }


def fulltext_handoff(ledger: list[dict[str, Any]], fulltext_index: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_src = {str(x.get("source_identity_reference") or ""): x for x in fulltext_index}
    out = []
    for row in ledger:
        if row["decision"] not in RETAINED:
            continue
        src = row["source_identity_reference"]
        ft = by_src.get(src)
        if not ft:
            continue
        path = Path(str(ft.get("text_path") or ""))
        digest = str(ft.get("full_text_sha256") or "")
        identity_review = str(ft.get("same_object_identity_review_reference") or "")
        if not path.as_posix() or not digest or not identity_review:
            raise ValueError(f"{src}: incomplete full-text identity/index row")
        payload = {
            "source_identity_reference": src,
            "retained_screening_decision_reference": row["decision_reference"],
            "retained_decision": row["decision"],
            "full_text_artifact_reference": str(ft.get("full_text_artifact_reference") or path),
            "full_text_sha256": digest,
            "full_text_revision_reference": f"fulltext-sha256:{digest}",
            "same_object_identity_review_reference": identity_review,
            "slr_source_unit": {
                "source_unit_ref": f"digital-esd:{src}:{digest}",
                "source_kind": "scholarly-full-text",
                "source_role": "screened-digital-esd-study",
                "language": str(ft.get("language") or "en"),
                "revision_ref": f"fulltext-sha256:{digest}",
                "text_path": str(path),
            },
            "canonical_slr_evidence_required": True,
            "reviewed_slr_evidence_required": True,
            "digital_esd_audit_projection_required": True,
            "source_audit_admission_required": True,
            "corpus_audited_source_required": True,
            "hyperfabric_audit_required": True,
            "framework_challenge_required": True,
            "screening_alone_creates_audit_admission": False,
            "slr_alone_creates_audit_admission": False,
        }
        payload["handoff_reference"] = stable_ref("digital-esd-p0g-handoff", payload)
        out.append(payload)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", required=True, type=Path)
    ap.add_argument("--out-dir", required=True, type=Path)
    ap.add_argument("--model-reference", default="digital-esd-baseline-candidate-assessor-v1")
    ap.add_argument("--family-threshold", type=float, default=0.72)
    ap.add_argument("--calibration-per-stratum", type=int, default=20)
    ap.add_argument("--pareto-limit", type=int, default=200)
    ap.add_argument("--fulltext-index", type=Path)
    args = ap.parse_args()

    ledger = load_screening_ledger(args.ledger)
    assessments = [candidate_assessment(r, args.model_reference) for r in ledger]
    hypotheses = build_family_hypotheses(ledger, args.family_threshold)
    calibration = calibration_queue(
        ledger, assessments, hypotheses, args.calibration_per_stratum
    )
    diagnostics = calibration_diagnostics(ledger, assessments)
    queue = pareto_queue(ledger, assessments, hypotheses, args.pareto_limit)

    fulltext_index = read_jsonl(args.fulltext_index) if args.fulltext_index else []
    handoffs = fulltext_handoff(ledger, fulltext_index) if fulltext_index else []
    denominator = denominator_receipt(ledger, hypotheses, fulltext_index)

    out = args.out_dir
    write_jsonl(out / "candidate-assessments.jsonl", assessments)
    write_jsonl(out / "study-family-hypotheses.jsonl", hypotheses)
    write_jsonl(out / "calibration-queue.jsonl", calibration)
    write_json(out / "calibration-diagnostics.json", diagnostics)
    write_jsonl(out / "pareto-review-queue.jsonl", queue)
    write_json(out / "denominator-integrity.json", denominator)
    if args.fulltext_index:
        write_jsonl(out / "p0g-fulltext-handoffs.jsonl", handoffs)

    manifest = {
        "schema": "digital-esd-adaptive-screening-p0-a-to-g-v1",
        "ledger_reference": str(args.ledger),
        "ledger_sha256": sha256_bytes(args.ledger.read_bytes()),
        "input_records": len(ledger),
        "candidate_assessments": len(assessments),
        "study_family_hypotheses": len(hypotheses),
        "calibration_queue": len(calibration),
        "pareto_queue": len(queue),
        "p0g_handoffs": len(handoffs),
        "candidate_layer_creates_screening_decision": False,
        "selector_creates_screening_decision": False,
        "duplicate_hypothesis_creates_study_identity": False,
        "unselected_record_may_leave_denominator": False,
        "screening_alone_creates_audit_admission": False,
        "slr_review_creates_audit_admission": False,
    }
    manifest["manifest_reference"] = stable_ref("digital-esd-p0-execution", manifest)
    write_json(out / "adaptive-screening-manifest.json", manifest)

    print(
        "DIGITAL_ESD_P0 "
        f"n0={len(ledger)} assessed={len(assessments)} "
        f"family_hypotheses={len(hypotheses)} calibration={len(calibration)} "
        f"pareto={len(queue)} p0g={len(handoffs)} "
        f"manifest={manifest['manifest_reference']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
