#!/usr/bin/env python3
"""Source-object audit for the purposively selected climate claim genealogy.

Originality guard: written as a reproducible *provenance inventory*, not a
machine-learning detector of climate denial or a representative national sample.
The original authors, producers and dates reside in the input CSV.

A cited primary producer/model may have many publications. A referenced
source-object can be: a model, a media article, a report, a quotation of another
report, a government press release, a transcription of an original speech, or
an unacquired underlying survey. Such things must NOT all be counted as
independent scientific analyses.  See docs/bom_fordham_temperature_claim_audit_20261024.md.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Mapping

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv"

# Audited same-commission source identities, not fuzzy title/source similarity.
# AEP's report, appendix, press release and Senate text identify one WM study.
# Future Group's 21/23 April release and ADL PDF identify one ADL study.
# These aliases do NOT imply the two consultant models share assumptions, nor
# that a press release is the original consultant-authored document itself.
SAME_ORIGINAL_MODEL = {
    "FUTURE_ADL_17B_2026": "ADL_2026_ORIGINAL",
    "WOODMAC_AEP_2026": "WOODMAC_ORIGINAL_2026",
}
# Dated ministry press release and departmental status page are separate
# original document objects despite reflecting the same policy design.
MUST_REMAIN_DISTINCT = (
    ("GOV_GAS_EXPOSURE_RELEASE_10SEP2026", "DCCEEW_GAS_REFORM_STATUS_29SEP2026"),
    ("GOV_GAS_BILL_14OCT2026", "HANSARD_GAS_PRINCIPAL_14OCT2026"),
    ("HANSARD_GAS_LEVY_14OCT2026", "ADL_2026_ORIGINAL"),
)

# Narrowly: original identifiable consultants/institute whose public estimates
# are named for these SPECIFIC outputs, not independent regressions, and not
# every author quoted by the press. ACTU's retrospective FY2023–24 WHAT-IF is
# its own policy calculation, *not* an extra forward 2026/27 model of $17bn.
NAMED_ESTIMATOR_ROOTS = {
    "GAS_TAX_17B_ANNUAL": ("TAI_TAX_17B_2025", "ADL_2026_ORIGINAL"),
    "GAS_INVESTMENT_TAX_83PC": ("WOODMAC_ORIGINAL_2026",),
    "GAS_ROYALTY_FREE_56PC": ("TAI_56PC_2024",),
}
# Which selected appearances make a direct published forward estimate/
# original consultant model claim; these are not rows from a random sample.
FORWARD_ESTIMATOR_RECEIPTS = {
    "GAS_TAX_17B_ANNUAL": ("G04", "G05", "G24"),
    "GAS_INVESTMENT_TAX_83PC": ("G10", "G32"),
    "GAS_ROYALTY_FREE_56PC": ("G01",),
}


def canonical_object(identifier: str) -> str:
    """Explicit *model* alias only; no other strings are silently merged."""
    return SAME_ORIGINAL_MODEL.get(identifier, identifier)


def observed_objects(row: Mapping[str, str]) -> set[str]:
    """Return cited upstream objects, not a set of independent originators."""
    return {canonical_object(s.strip())
            for s in row["evidence_objects"].split("|") if s.strip()}


def read_ledger(path: Path = LEDGER) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    required = {
        "receipt_id", "claim_family", "date", "originator_or_speaker",
        "surface_or_document", "relation_to_claim", "evidence_objects",
        "numerical_or_rhetorical_payload", "provenance_scope", "locator",
        "nonpromotion_boundary",
    }
    if not rows or not required.issubset(rows[0]):
        raise ValueError("Missing expected claim-genealogy schema")
    ids = [r["receipt_id"] for r in rows]
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate receipt IDs")
    for r in rows:
        if any(not r[k] for k in required) or not r["locator"].startswith("https://"):
            raise ValueError("Missing required source or HTTPS locator: " + r["receipt_id"])
    return rows


def audit(rows: Iterable[Mapping[str, str]]) -> dict:
    rows = list(rows)
    byid = {r["receipt_id"]: r for r in rows}
    byfamily: dict[str, list] = defaultdict(list)
    for r in rows:
        byfamily[r["claim_family"]].append(r)
    for a, b in MUST_REMAIN_DISTINCT:
        if canonical_object(a) == canonical_object(b):
            raise ValueError("Invalid alias merges distinct original source objects")
    if "G39" in byid and "G40" in byid:
        a, b = (observed_objects(byid[k]) for k in ("G39", "G40"))
        if a == b:
            raise ValueError("Distinct September release and status page conflated")
    if "G05" in byid and "G24" in byid:
        if observed_objects(byid["G05"]) != observed_objects(byid["G24"]):
            raise ValueError("Future Group release and original ADL consultant model unjoined")
    if "G10" in byid and "G32" in byid:
        if observed_objects(byid["G10"]) != observed_objects(byid["G32"]):
            raise ValueError("AEP media and original WM consultant model unjoined")
    findings = {}
    for family, family_rows in sorted(byfamily.items()):
        objects = set().union(*(observed_objects(r) for r in family_rows))
        reasons = Counter(r["relation_to_claim"] for r in family_rows)
        findings[family] = {
            "sampled_appearances": len(family_rows),
            "cited_object_ids": sorted(objects),
            "cited_object_count_not_independence": len(objects),
            "relation_classes": dict(sorted(reasons.items())),
            "named_estimator_model_roots_not_statistical_independence": list(
                NAMED_ESTIMATOR_ROOTS.get(family, ())
            ),
        }
    for family, wanted in NAMED_ESTIMATOR_ROOTS.items():
        got = set(findings.get(family, {}).get("cited_object_ids", []))
        if not set(wanted).issubset(got):
            raise ValueError("Named original estimator missing for " + family)
        for k in FORWARD_ESTIMATOR_RECEIPTS[family]:
            if k not in byid or byid[k]["claim_family"] != family:
                raise ValueError("Specific first-party original receipt missing: " + k)
    if "G06" in byid and not "underdetermined" in byid["G06"]["relation_to_claim"]:
        raise ValueError("April 14 Greens claim cannot be assigned to later ADL release")
    return {
        "status": "selected-source-provenance-only",
        "sampled_appearances": len(rows),
        "sampled_claim_families": len(byfamily),
        "family_audit": findings,
        "warning": (
            "No national source-concentration estimate, percentage of climate "
            "denialists, independently validated model count or causal donor "
            "influence follows from this purposive ledger."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=LEDGER)
    parser.add_argument("--json", action="store_true", help="machine-readable stdout")
    args = parser.parse_args()
    report = audit(read_ledger(args.ledger))
    if args.json:
        print(json.dumps(report, sort_keys=True, indent=2))
    else:
        print("Sampled appearance records:", report["sampled_appearances"])
        print("Selected proposition families:", report["sampled_claim_families"])
        for family, values in report["family_audit"].items():
            if family in NAMED_ESTIMATOR_ROOTS:
                print(f"{family}: {values['sampled_appearances']} appearances; "
                      f"{len(values['named_estimator_model_roots_not_statistical_independence'])} "
                      "named public model-producer roots (NOT independent verification)")
        print(report["warning"])


if __name__ == "__main__":
    main()
