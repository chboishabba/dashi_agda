#!/usr/bin/env python3
"""Build Digital-ESD calibration diagnostics and a fail-closed Pareto review queue.

Consumes candidate-only assessments plus the authoritative screening ledger.
It never writes screening decisions.

Outputs:
  calibration-selection.jsonl
  calibration-estimate.json
  screening-pareto-queue.jsonl
  pareto-manifest.json

The Pareto axes match the formal owner:
  information-gain loss
  likely corpus-contraction loss
  rare-cell coverage loss
  duplicate-family payoff loss
  reviewer cost

Lower is better per coordinate. No scalar total is calculated.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from collections import Counter
from pathlib import Path
from typing import Any


AXES = (
    "information_gain_loss_cost",
    "corpus_contraction_loss_cost",
    "rare_cell_coverage_loss_cost",
    "duplicate_family_payoff_loss_cost",
    "reviewer_cost",
)


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")


def sha256_json(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    out = []
    with path.open("r", encoding="utf-8") as handle:
        for n, line in enumerate(handle, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: expected object")
            out.append(row)
    return out


def stable_order_key(source_ref: str, salt: str) -> str:
    return hashlib.sha256((salt + "\0" + source_ref).encode("utf-8")).hexdigest()


def authoritative_reviewed(row: dict[str, Any]) -> bool:
    decision = str(row.get("decision") or "")
    reviewer = str(row.get("reviewer_or_model_reference") or "")
    return decision != "unresolved" or reviewer not in {"", "unassigned"}


def publication_type_key(row: dict[str, Any]) -> str:
    snap = row.get("title_abstract_snapshot") or {}
    value = snap.get("publication_type")
    if isinstance(value, list):
        return "|".join(sorted(str(x) for x in value))
    return str(value or "unknown")


def abstract_length(row: dict[str, Any]) -> int:
    snap = row.get("title_abstract_snapshot") or {}
    return len(str(snap.get("abstract") or ""))


def load_fibre_memberships(path: Path | None) -> dict[str, int]:
    out: dict[str, int] = {}
    if path is None or not path.exists():
        return out
    for fibre in read_jsonl(path):
        members = [str(x) for x in fibre.get("member_source_references", [])]
        size = len(members)
        for ref in members:
            out[ref] = max(size, out.get(ref, 0))
    return out


def choose_stratum(
    ledger: dict[str, Any],
    assessment: dict[str, Any],
    fibre_size: int,
    type_frequency: int,
    rare_cutoff: int,
) -> str:
    reasons = set(str(x) for x in assessment.get("candidate_reason_codes", []))
    candidate = str(assessment.get("candidate_decision") or "unresolved")
    confidence = str(assessment.get("confidence_reference") or "")

    if "inaccessibleAbstract" in reasons or abstract_length(ledger) == 0:
        return "missingAbstractOrMalformedMetadata"
    if fibre_size >= 2:
        return "highDuplicateAmbiguity"
    if type_frequency <= rare_cutoff:
        return "rareTerminologyOrSourceType"
    if candidate in {"include", "probable"} and confidence.startswith("high"):
        return "obviousIncludeCandidate"
    if candidate == "exclude" and confidence.startswith("high"):
        return "obviousExcludeCandidate"
    return "highUncertaintyCandidate"


def costs(stratum: str, ledger: dict[str, Any], fibre_size: int) -> dict[str, int]:
    info = {
        "highUncertaintyCandidate": 0,
        "missingAbstractOrMalformedMetadata": 1,
        "rareTerminologyOrSourceType": 1,
        "highDuplicateAmbiguity": 2,
        "obviousIncludeCandidate": 4,
        "obviousExcludeCandidate": 4,
    }[stratum]
    contraction = 0 if stratum == "obviousExcludeCandidate" else (1 if stratum == "highDuplicateAmbiguity" else 3)
    rare = 0 if stratum == "rareTerminologyOrSourceType" else 5
    duplicate = max(0, 8 - min(fibre_size, 8)) if fibre_size >= 2 else 8

    n = abstract_length(ledger)
    if n == 0:
        reviewer = 2
    elif n <= 1000:
        reviewer = 1
    elif n <= 2500:
        reviewer = 2
    elif n <= 5000:
        reviewer = 3
    else:
        reviewer = 4

    return {
        "information_gain_loss_cost": info,
        "corpus_contraction_loss_cost": contraction,
        "rare_cell_coverage_loss_cost": rare,
        "duplicate_family_payoff_loss_cost": duplicate,
        "reviewer_cost": reviewer,
    }


def dominates(a: dict[str, Any], b: dict[str, Any]) -> bool:
    le = all(int(a[k]) <= int(b[k]) for k in AXES)
    lt = any(int(a[k]) < int(b[k]) for k in AXES)
    return le and lt


def pareto_front(rows: list[dict[str, Any]]) -> set[str]:
    front: set[str] = set()
    for i, row in enumerate(rows):
        if not any(i != j and dominates(other, row) for j, other in enumerate(rows)):
            front.add(str(row["source_identity_reference"]))
    return front


def calibration_diagnostics(
    ledger_by_ref: dict[str, dict[str, Any]],
    assessment_by_ref: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    reviewed_refs = [ref for ref, row in ledger_by_ref.items() if authoritative_reviewed(row)]
    pairs = []
    for ref in reviewed_refs:
        assessment = assessment_by_ref.get(ref)
        if assessment is None:
            continue
        actual = str(ledger_by_ref[ref].get("decision") or "unresolved")
        candidate = str(assessment.get("candidate_decision") or "unresolved")
        pairs.append((actual, candidate))

    confusion = Counter(pairs)
    positive = sum(1 for actual, _ in pairs if actual in {"include", "probable"})
    false_negative_proxy_n = sum(
        1 for actual, candidate in pairs
        if actual in {"include", "probable"} and candidate == "exclude"
    )
    disagreement_n = sum(1 for actual, candidate in pairs if actual != candidate)
    unresolved_after_review = sum(
        1 for ref in reviewed_refs if ledger_by_ref[ref].get("decision") == "unresolved"
    )

    false_negative_proxy = (
        false_negative_proxy_n / positive if positive else None
    )
    return {
        "schema": "digital-esd-screening-calibration-estimate-v1",
        "reviewed_pair_count": len(pairs),
        "reviewed_positive_count": positive,
        "candidate_false_negative_proxy_n": false_negative_proxy_n,
        "candidate_false_negative_proxy": false_negative_proxy,
        "candidate_review_disagreement_n": disagreement_n,
        "candidate_review_disagreement_rate": disagreement_n / len(pairs) if pairs else None,
        "explicitly_reviewed_unresolved_n": unresolved_after_review,
        "confusion_counts": {
            f"{actual}->{candidate}": n
            for (actual, candidate), n in sorted(confusion.items())
        },
        "estimate_scope_reference": "reviewed calibration subset only; not population truth",
        "estimate_creates_source_truth": False,
        "estimate_creates_population_truth": False,
        "estimate_creates_automatic_decision": False,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", type=Path, required=True)
    ap.add_argument("--assessments", type=Path, required=True)
    ap.add_argument("--fibres", type=Path)
    ap.add_argument("--out-dir", type=Path, default=Path("artifacts/digital-esd/screening/adaptive"))
    ap.add_argument("--calibration-per-stratum", type=int, default=25)
    ap.add_argument("--rare-type-max", type=int)
    ap.add_argument("--selection-salt", default="digital-esd-calibration-v1")
    args = ap.parse_args()

    ledger_rows = read_jsonl(args.ledger)
    assessment_rows = read_jsonl(args.assessments)
    ledger_by_ref = {str(r["source_identity_reference"]): r for r in ledger_rows}
    assessment_by_ref = {str(r["source_identity_reference"]): r for r in assessment_rows}
    if set(assessment_by_ref) != set(ledger_by_ref):
        missing_a = sorted(set(ledger_by_ref) - set(assessment_by_ref))
        missing_l = sorted(set(assessment_by_ref) - set(ledger_by_ref))
        raise RuntimeError(
            f"assessment/ledger identity mismatch: missing assessments={missing_a[:10]} "
            f"missing ledger={missing_l[:10]}"
        )

    fibre_sizes = load_fibre_memberships(args.fibres)
    type_counts = Counter(publication_type_key(row) for row in ledger_rows)
    rare_cutoff = args.rare_type_max
    if rare_cutoff is None:
        rare_cutoff = max(5, math.ceil(len(ledger_rows) * 0.005))

    queue: list[dict[str, Any]] = []
    by_stratum: dict[str, list[str]] = {}
    for ref, ledger in ledger_by_ref.items():
        if str(ledger.get("decision") or "") != "unresolved":
            continue
        assessment = assessment_by_ref[ref]
        ptype = publication_type_key(ledger)
        fibre_size = fibre_sizes.get(ref, 0)
        stratum = choose_stratum(
            ledger,
            assessment,
            fibre_size,
            type_counts[ptype],
            rare_cutoff,
        )
        by_stratum.setdefault(stratum, []).append(ref)
        row = {
            "schema": "digital-esd-screening-pareto-candidate-v1",
            "source_identity_reference": ref,
            "candidate_assessment_reference": assessment["assessment_reference"],
            "family_hypothesis_reference": (
                f"candidate-fibre-size:{fibre_size}" if fibre_size else "no-candidate-fibre"
            ),
            "calibration_stratum_reference": stratum,
            "publication_type_frequency": type_counts[ptype],
            "candidate_only": True,
            "pending_explicit_review": True,
            "selection_creates_screening_decision": False,
            "selection_creates_exclusion": False,
        }
        row.update(costs(stratum, ledger, fibre_size))
        queue.append(row)

    front = pareto_front(queue)
    for row in queue:
        row["pareto_front"] = row["source_identity_reference"] in front

    queue.sort(
        key=lambda row: (
            not row["pareto_front"],
            tuple(int(row[k]) for k in AXES),
            stable_order_key(row["source_identity_reference"], args.selection_salt),
        )
    )

    args.out_dir.mkdir(parents=True, exist_ok=True)
    queue_path = args.out_dir / "screening-pareto-queue.jsonl"
    with queue_path.open("w", encoding="utf-8") as fh:
        for row in queue:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    calibration_rows = []
    for stratum, refs in sorted(by_stratum.items()):
        refs = sorted(refs, key=lambda ref: stable_order_key(ref, args.selection_salt + stratum))
        for ref in refs[: args.calibration_per_stratum]:
            payload = {
                "source_identity_reference": ref,
                "stratum": stratum,
                "selection_process_reference": "deterministic-stratified-calibration:v1",
            }
            calibration_rows.append({
                "schema": "digital-esd-calibration-selection-v1",
                "source_identity_reference": ref,
                "stratum": stratum,
                "stratum_evidence_reference": assessment_by_ref[ref]["assessment_reference"],
                "selection_reference": "calibration-selection:" + sha256_json(payload),
                "selection_process_reference": "deterministic-stratified-calibration:v1",
                "selected_for_explicit_review": True,
                "selection_creates_decision": False,
            })

    calibration_path = args.out_dir / "calibration-selection.jsonl"
    with calibration_path.open("w", encoding="utf-8") as fh:
        for row in calibration_rows:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    estimate = calibration_diagnostics(ledger_by_ref, assessment_by_ref)
    estimate["reviewed_calibration_set_reference"] = str(args.ledger)
    estimate["rubric_version"] = next(iter(ledger_rows), {}).get("screening_rubric_version")
    estimate["residual_class_reference"] = "screening-pareto-queue:" + sha256_json(
        [{"ref": r["source_identity_reference"], "stratum": r["calibration_stratum_reference"]} for r in queue]
    )
    estimate_path = args.out_dir / "calibration-estimate.json"
    estimate_path.write_text(
        json.dumps(estimate, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    manifest = {
        "schema": "digital-esd-screening-pareto-manifest-v1",
        "ledger_reference": str(args.ledger),
        "assessment_reference": str(args.assessments),
        "candidate_fibres_reference": str(args.fibres) if args.fibres else None,
        "unresolved_queue_count": len(queue),
        "pareto_front_count": len(front),
        "calibration_selection_count": len(calibration_rows),
        "stratum_counts": {k: len(v) for k, v in sorted(by_stratum.items())},
        "pareto_axes": list(AXES),
        "scalar_score_used": False,
        "pareto_priority_creates_screening_decision": False,
        "pareto_priority_creates_exclusion": False,
        "unreviewed_records_removed_from_denominator": False,
    }
    (args.out_dir / "pareto-manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
