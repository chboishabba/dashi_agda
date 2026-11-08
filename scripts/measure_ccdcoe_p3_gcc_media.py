#!/usr/bin/env python3
"""Reproducible DESCRIPTIVE coding of independently reviewed media items.

Input JSONL: id, source_sha256, outlet, date (YYYY-MM-DD), treatment
("GCC-linked-outlet"|"comparison-outlet"), period ("before"|"after"),
frame ("science_uncertainty"|"economic_cost"|"consensus_acknowledgement"|
"policy_mandate"|"other_or_undetermined"), coder_id, review_receipt,
source_text_reviewed (true).

Per-article rows MUST come from original full text, not archive indexes.
The output has observed frame proportions and descriptive differences-in-
differences; it is NOT a causal effect without a separate research design.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
from math import sqrt

FRAMES = {"science_uncertainty", "economic_cost",
          "consensus_acknowledgement", "policy_mandate",
          "other_or_undetermined"}
ARMS = {"GCC-linked-outlet", "comparison-outlet"}
PERIODS = {"before", "after"}
REQUIRED = {"id","source_sha256","outlet","date","treatment",
            "period","frame","coder_id","review_receipt","source_text_reviewed"}

def wilson(success: int, n: int, z: float = 1.96) -> list[float]:
    if n <= 0:
        raise ValueError("Wilson interval requires observed denominator")
    p = success / n
    d = 1.0 + z*z/n
    center = (p + z*z/(2*n))/d
    half = z * sqrt(p*(1-p)/n + z*z/(4*n*n))/d
    return [round(max(0.0,center-half),6),round(min(1.0,center+half),6)]

def analyse(rows: list[dict], focus: str) -> dict:
    if focus not in FRAMES - {"other_or_undetermined"}:
        raise ValueError("Invalid substantive frame")
    seen = set()
    cells: dict[tuple[str,str], list[bool]] = {
        (arm,period):[] for arm in ARMS for period in PERIODS}
    outlets: dict[tuple[str,str], set[str]] = {
        (arm,period):set() for arm in ARMS for period in PERIODS}
    for row in rows:
        if not REQUIRED <= row.keys():
            raise ValueError("Missing required article provenance fields")
        rid = row["id"]
        if not isinstance(rid,str) or not rid or rid in seen:
            raise ValueError("Duplicate or invalid document identity")
        seen.add(rid)
        if row["treatment"] not in ARMS or row["period"] not in PERIODS:
            raise ValueError("Unrecognised study arm or period")
        if row["frame"] not in FRAMES:
            raise ValueError("Unknown frame")
        if not row["source_text_reviewed"] or not row["review_receipt"]:
            raise ValueError("Only original full-text reviewed observations admitted")
        if not row["coder_id"] or not row["outlet"]:
            raise ValueError("Coder/outlet required")
        digest = row["source_sha256"]
        if not isinstance(digest,str) or len(digest)!=64 or any(
            c not in "0123456789abcdef" for c in digest):
            raise ValueError("Original document SHA256 required")
        from datetime import date
        try:
            dt=date.fromisoformat(row["date"])
        except (ValueError,TypeError):
            raise ValueError("Invalid article date") from None
        if row["period"] == "before" and dt.year >= 1994:
            raise ValueError("Before treatment marked after plausible 1993 campaign")
        if row["period"] == "after" and dt.year < 1993:
            raise ValueError("After treatment marked before 1993")
        key=(row["treatment"],row["period"])
        cells[key].append(row["frame"]==focus)
        outlets[key].add(row["outlet"])
    if any(not x for x in cells.values()):
        raise ValueError("All four arm/period groups require reviewed articles")
    counts = {}
    for arm in sorted(ARMS):
        for period in sorted(PERIODS):
            key=(arm,period)
            observed=cells[key]
            n=len(observed)
            k=sum(observed)
            counts[f"{arm}:{period}"]={
                "documents":n,"frame_count":k,
                "frame_proportion":round(k/n,6),
                "wilson_95_descriptive":wilson(k,n),
                "outlets":sorted(outlets[key])}
    t="GCC-linked-outlet"
    c="comparison-outlet"
    proportion=lambda arm,p: sum(cells[(arm,p)])/len(cells[(arm,p)])
    descriptive_did=(proportion(t,"after")-proportion(t,"before")-
                     proportion(c,"after")+proportion(c,"before"))
    return {"schema":"dashi.ccdcoe.p3.gcc_media_descriptive.v1",
            "focus":focus,"article_count":len(rows),
            "counts":counts,
            "descriptive_difference_in_differences":round(descriptive_did,6),
            "causal_attribution":"NOT_IDENTIFIED",
            "limitations":["Sampling frame selection has not been validated by this code",
                           "The treatment contrast can be confounded by concurrent events",
                           "Article clustering/outlet dependence not addressed by Wilson intervals",
                           "The measured contrast does not estimate policy or audience persuasion"]}

def self_test() -> None:
    from datetime import date
    synthetic=[]
    for arm in sorted(ARMS):
        for period in sorted(PERIODS):
            for i in range(3):
                synthetic.append({
                    "id":f"synthetic-{arm}-{period}-{i}",
                    "source_sha256":hashlib.sha256(
                        f"synthetic-{arm}-{period}-{i}".encode()).hexdigest(),
                    "outlet":f"SYNTHETIC {arm}","date":
                        "1992-05-01" if period=="before" else "1994-05-01",
                    "treatment":arm,"period":period,
                    "frame":"science_uncertainty" if i==0 or (
                        arm=="GCC-linked-outlet" and period=="after") else "other_or_undetermined",
                    "coder_id":"SYNTHETIC","review_receipt":"SYNTHETIC-NOT-ACTUAL",
                    "source_text_reviewed":True})
    result=analyse(synthetic,"science_uncertainty")
    assert result["article_count"]==12
    assert result["causal_attribution"]=="NOT_IDENTIFIED"
    assert result["descriptive_difference_in_differences"]==0.666667
    try:
        analyse(synthetic[:-3],"science_uncertainty")
    except ValueError:
        pass
    else:
        raise AssertionError("Missing comparison cell accepted")
    broken=[dict(x) for x in synthetic]
    broken[0]["review_receipt"]=None
    try:
        analyse(broken,"science_uncertainty")
    except ValueError:
        pass
    else:
        raise AssertionError("Unreviewed document admitted")
    print("PASS: synthetic 2x2 descriptives, Wilson limits, no-causality, missing-cell and review guards")

def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input",type=Path)
    p.add_argument("--output",type=Path)
    p.add_argument("--focus",default="science_uncertainty")
    p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    if a.self_test:
        self_test()
        return
    if a.input is None or a.output is None:
        p.error("--input and --output required")
    rows=[json.loads(line) for line in a.input.read_text(encoding="utf-8").splitlines() if line.strip()]
    result=analyse(rows,a.focus)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n",encoding="utf-8")
    print(f"Wrote descriptive results for {result['article_count']} reviewed items; causal attribution NOT IDENTIFIED")

if __name__=="__main__":
    main()
