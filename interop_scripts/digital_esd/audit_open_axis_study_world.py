#!/usr/bin/env python3
"""Read-only, source-bound n-axis coverage audit for already decomposed ESD studies.

This is a validation/projection sidecar over existing reviewed study part and
SLR/PNF receipts, NOT a new canonical evidence substrate, parser, reviewer,
or 43,996-row synthetic world. It never approves empirical admission.

Input schema (JSON object):
  {
    "axis_registry_revision": "...",
    "axes": [{"axis_ref":"...", "meaning":"..."}],
    "parts": [{
       "source_ref":"...", "source_revision_ref":"...", "part_ref":"...",
       "part_kind":"...", "decomposition_receipt_ref":"..."
    }],
    "accounts": [{
       "source_ref":"...", "part_ref":"...", "axis_ref":"...",
       "state":"direct_reviewed|conditional|contested|unmeasured|inaccessible|not_applicable",
       "reason":"...", "...status-specific receipt refs":"..."
    }],
    "relations": [{
      "relation_ref":"...", "participants":[{"source_ref":"...","part_ref":"..."}],
      "axes":["..."], "valence":{"kind":"scalar|balanced_ternary","value":...},
      "epistemic_status":"candidate|reviewed|contested|unresolved",
      "source_and_context_receipt_refs":["..."]
    }]
  }

A complete *ledger* still does not establish that all study parts were found,
that candidate SLR spans were reviewed, or that source claims are true.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

STATES = {
    "direct_reviewed", "conditional", "contested",
    "unmeasured", "inaccessible", "not_applicable", "source_reported_pending_review",
    "not_yet_assessed",
}
EVIDENCE_FOR_DIRECT = (
    "reviewed_packet_ref", "reviewed_observation_ref",
    "fulltext_revision_ref", "evidence_span_ref",
    "source_audit_observation_membership_ref",
    "part_axis_relevance_review_ref", "source_audit_admission_ref",
)
EVIDENCE_FOR_CONDITIONAL = (
    "premise_ref", "condition_ref", "transfer_limitation_ref",
)
EVIDENCE_FOR_CONTESTED = (
    "position_ref", "counterposition_ref", "dispute_ref",
)

def required_string(row: dict[str, Any], field: str, context: str) -> str:
    value = row.get(field)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{context}: missing nonempty {field}")
    return value.strip()

def require_distinct(values: list[str], context: str) -> None:
    if len(set(values)) != len(values):
        raise ValueError(f"{context}: duplicate identifier")

def validate(value: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError("input must be a JSON object")
    required_string(value, "axis_registry_revision", "world")
    axes = value.get("axes")
    parts = value.get("parts")
    accounts = value.get("accounts")
    relations = value.get("relations", [])
    if not all(isinstance(v, list) for v in (axes, parts, accounts, relations)):
        raise ValueError("axes/parts/accounts/relations must be lists")
    if not axes or not parts:
        raise ValueError("an empty declared axis or study-part universe is not an admitted world")

    required_string(value, "part_taxonomy_revision", "world")
    required_part_kinds = value.get("required_part_kinds")
    if not isinstance(required_part_kinds, list) or not required_part_kinds:
        raise ValueError("world: nonempty source-declared required_part_kinds needed")
    required_roles = [
        required_string({"role": role}, "role", "required part kind")
        for role in required_part_kinds
    ]
    require_distinct(required_roles, "required_part_kinds")

    axis_ids = [required_string(a, "axis_ref", "axis") for a in axes]
    for axis in axes:
        required_string(axis, "meaning", "axis")
    require_distinct(axis_ids, "axes")
    axis_set = set(axis_ids)

    part_ids = []
    revision_by_source: dict[str, str] = {}
    parts_by_source = Counter()
    part_roles_by_source: dict[str, set[str]] = defaultdict(set)
    for part in parts:
        source = required_string(part, "source_ref", "part")
        rev = required_string(part, "source_revision_ref", "part")
        ident = required_string(part, "part_ref", "part")
        kind = required_string(part, "part_kind", "part")
        required_string(part, "decomposition_receipt_ref", "part")
        if source in revision_by_source and revision_by_source[source] != rev:
            raise ValueError(f"{source}: different source revisions need separate versioned source identities")
        revision_by_source[source] = rev
        part_ids.append((source, ident))
        parts_by_source[source] += 1
        part_roles_by_source[source].add(kind)
    if len(set(part_ids)) != len(part_ids):
        raise ValueError("duplicate source/part identity")
    part_set = set(part_ids)
    for source, found in part_roles_by_source.items():
        absent_roles = sorted(set(required_roles) - found)
        if absent_roles:
            raise ValueError(f"{source}: missing declared required study part kinds {absent_roles}")

    status_counts = Counter()
    indexed = set()
    warnings = []
    for a in accounts:
        source = required_string(a, "source_ref", "axis account")
        part = required_string(a, "part_ref", "axis account")
        axis = required_string(a, "axis_ref", "axis account")
        state = required_string(a, "state", "axis account")
        reason = required_string(a, "reason", "axis account")
        key = (source, part, axis)
        if (source, part) not in part_set or axis not in axis_set:
            raise ValueError(f"axis account references undeclared part/axis: {key}")
        if key in indexed:
            raise ValueError(f"duplicate part-axis account: {key}")
        indexed.add(key)
        if state not in STATES:
            raise ValueError(f"{key}: unknown evidence state {state}")
        status_counts[state] += 1
        if state == "direct_reviewed":
            for field in EVIDENCE_FOR_DIRECT:
                required_string(a, field, f"reviewed account {key}")
            if a["fulltext_revision_ref"] != revision_by_source[source]:
                raise ValueError(f"{key}: reviewed evidence revision != study full-text revision")
            # References are pointers. Membership itself is proved in Agda,
            # and must not be certified merely by asserting a JSON boolean.
            warnings.append(f"{key}: external reviewed membership and relevance proofs require verification")
        elif state == "source_reported_pending_review":
            for field in ("source_section_ref", "reported_observation_ref", "review_debt_ref"):
                required_string(a, field, f"source-reported pending-review account {key}")
        elif state == "not_yet_assessed":
            required_string(a, "review_work_ref", f"pending part-axis account {key}")
        elif state == "conditional":
            for field in EVIDENCE_FOR_CONDITIONAL:
                required_string(a, field, f"conditional account {key}")
        elif state == "contested":
            for field in EVIDENCE_FOR_CONTESTED:
                required_string(a, field, f"contested account {key}")
        elif state == "not_applicable":
            required_string(a, "inapplicability_justification_ref", f"inapplicable account {key}")
        elif state == "inaccessible":
            required_string(a, "access_constraint_ref", f"inaccessible account {key}")
        elif state == "unmeasured":
            required_string(a, "missing_observation_ref", f"unmeasured account {key}")
            required_string(a, "reviewed_source_scope_ref", f"reviewed unmeasured account {key}")

    expected = {(source, part, axis) for source, part in part_set for axis in axis_set}
    missing = sorted(expected - indexed)
    if missing:
        raise ValueError(f"axis accounting incomplete: {len(missing)} missing; first={missing[:5]}")

    parent = {p: p for p in part_set}
    def find(p: tuple[str, str]) -> tuple[str, str]:
        while parent[p] != p:
            parent[p] = parent[parent[p]]
            p = parent[p]
        return p
    def union(p: tuple[str, str], q: tuple[str, str]) -> None:
        parent[find(q)] = find(p)

    counts_by_arity = Counter()
    for relation in relations:
        r = required_string(relation, "relation_ref", "relation")
        endpoints = relation.get("participants")
        if not isinstance(endpoints, list) or not endpoints:
            raise ValueError(f"{r}: requires at least one source-bound study part")
        points = [(required_string(p, "source_ref", r),
                   required_string(p, "part_ref", r)) for p in endpoints]
        for point in points:
            if point not in part_set:
                raise ValueError(f"{r}: unknown source/part {point}")
        if len(set(points)) != len(points):
            raise ValueError(f"{r}: duplicate participant")
        raxes = relation.get("axes")
        if not isinstance(raxes, list) or not raxes or set(raxes) - axis_set:
            raise ValueError(f"{r}: axes must be a nonempty subset of the declared n-axis family")
        valence = relation.get("valence", {})
        kind, v = valence.get("kind"), valence.get("value")
        if kind == "unscored":
            if v is not None:
                raise ValueError(f"{r}: unscored relation cannot carry a scalar or ternary value")
            if relation.get("epistemic_status") not in ("candidate", "unresolved", "contested"):
                raise ValueError(f"{r}: unscored relation cannot be promoted to reviewed")
        elif kind == "balanced_ternary":
            if v not in ("neg", "zero", "pos"):
                raise ValueError(f"{r}: balanced ternary must be neg/zero/pos")
        elif kind == "scalar":
            if not isinstance(v, (int, float)) or isinstance(v, bool):
                raise ValueError(f"{r}: scalar valence must be numeric")
        else:
            raise ValueError(f"{r}: invalid relation valence kind")
        if relation.get("epistemic_status") not in ("candidate", "reviewed", "contested", "unresolved"):
            raise ValueError(f"{r}: independent epistemic status required; ternary zero is not N/A")
        provenance = relation.get("source_and_context_receipt_refs")
        if not isinstance(provenance, list) or not provenance or not all(isinstance(x, str) and x.strip() for x in provenance):
            raise ValueError(f"{r}: missing source/context provenance references")
        for p in points[1:]:
            union(points[0], p)
        counts_by_arity[len(points)] += 1

    components = defaultdict(list)
    for point in sorted(part_set):
        components[find(point)].append({"source_ref": point[0], "part_ref": point[1]})
    ordered_components = sorted(components.values(), key=lambda xs: (xs[0]["source_ref"], xs[0]["part_ref"]))
    canonical = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {
        "schema": "digital-esd-n-axis-candidate-world-audit-v1",
        "input_sha256": hashlib.sha256(canonical).hexdigest(),
        "axis_registry_revision": value["axis_registry_revision"],
        "part_taxonomy_revision": value["part_taxonomy_revision"],
        "required_part_kinds": required_roles,
        "axis_count": len(axis_set),
        "source_count": len(revision_by_source),
        "declared_study_part_count": len(part_set),
        "account_count": len(indexed),
        "accounting_is_total_over_declared_parts_and_axes": True,
        "decomposition_completeness_independently_verified": False,
        "direct_reviewed_structural_receipt_count": status_counts["direct_reviewed"],
        "evidence_state_counts": dict(sorted(status_counts.items())),
        "relation_arity_counts": dict(sorted(counts_by_arity.items())),
        "connected_components_over_declared_parts": ordered_components,
        "reviewed_evidence_and_source_admission_verified": False,
        "unassessed_part_axis_count": status_counts["not_yet_assessed"],
        "published_pending_review_part_axis_count": status_counts["source_reported_pending_review"],
        "all_part_axis_reviews_closed": (status_counts["not_yet_assessed"] == 0 and
                                         status_counts["source_reported_pending_review"] == 0),
        "empirical_world_admitted": False,
        "warnings": warnings,
    }

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    payload = json.loads(args.input.read_text(encoding="utf-8"))
    result = validate(payload)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"ESD_OPEN_AXIS_AUDIT axes={result['axis_count']} parts={result['declared_study_part_count']} components={len(result['connected_components_over_declared_parts'])} candidate_only=true")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
