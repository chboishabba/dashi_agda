#!/usr/bin/env python3
"""Source-bound Follow Through ranking sensitivity; no synthetic historical data."""
import argparse
import csv
import json
from collections import defaultdict
from decimal import Decimal, InvalidOperation
from pathlib import Path

REQUIRED = ("source_id", "page", "model", "site", "cohort",
            "domain", "instrument", "specification", "effect",
            "weight", "status")
ALLOWED = {"inspected-original", "verified-transcription"}

def load(path):
    with open(path, newline="", encoding="utf-8") as fh:
        reader = csv.DictReader(fh)
        missing = set(REQUIRED) - set(reader.fieldnames or ())
        if missing:
            raise ValueError("Missing columns: " + ", ".join(sorted(missing)))
        records = []
        keys = set()
        for line, row in enumerate(reader, 2):
            if any(not (row[k] or "").strip() for k in REQUIRED):
                raise ValueError(f"row {line}: missing provenance or value; do not impute")
            if row["status"] not in ALLOWED:
                raise ValueError(f"row {line}: inadmissible source inspection status")
            try:
                e = Decimal(row["effect"])
                w = Decimal(row["weight"])
            except InvalidOperation:
                raise ValueError(f"row {line}: nonnumeric effect or weight")
            if not e.is_finite() or not w.is_finite() or w <= 0:
                raise ValueError(f"row {line}: non-finite or nonpositive values")
            key = tuple(row[k] for k in
                        ("model", "site", "cohort", "domain",
                         "instrument", "specification"))
            if key in keys:
                raise ValueError(f"row {line}: duplicate analysis cell {key}")
            keys.add(key)
            records.append((row, e, w))
    if not records:
        raise ValueError("empty evidence file")
    return records

def analyze(rows):
    # Restrict model comparisons to exactly shared site/cohort/instrument
    # before averaging; do not compare different measurement surfaces.
    groups = defaultdict(list)
    for r,e,w in rows:
        groups[(r["domain"], r["instrument"], r["specification"])].append((r,e,w))
    output = []
    for (domain,instrument,spec), vals in sorted(groups.items()):
        by_model = defaultdict(dict)
        for r,e,w in vals:
            by_model[r["model"]][(r["site"],r["cohort"])] = (e,w)
        common = set.intersection(*(set(x) for x in by_model.values()))
        if not common or len(by_model) < 2:
            output.append(dict(domain=domain,instrument=instrument,
                specification=spec,status="incomparable",reason="no common sites/cohorts or models"))
            continue
        means = {}
        for model, cells in by_model.items():
            # Model-specific weights imply different estimands if not matched.
            denom = sum((cells[k][1] for k in common),Decimal(0))
            means[model] = sum((cells[k][0]*cells[k][1] for k in common),Decimal(0))/denom
        ordered = sorted(means, key=lambda m:(-means[m],m))
        output.append(dict(domain=domain,instrument=instrument,
            specification=spec,status="descriptive-only",
            matched_sites=len(common),matched_models=len(by_model),
            ranking=[dict(model=m,mean=str(means[m])) for m in ordered],
            warning="Not randomised causal effect; no confidence intervals, covariate adjustment or attrition corrections supplied"))
    return output

def main():
    p=argparse.ArgumentParser()
    p.add_argument("csv",type=Path,help="Actual sourced estimates, never chart-traced guesses")
    a=p.parse_args()
    print(json.dumps(analyze(load(a.csv)),indent=2))

if __name__=="__main__":
    main()
