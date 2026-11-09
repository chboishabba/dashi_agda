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
import hashlib
import json
from pathlib import Path
import tempfile
from math import sqrt
from datetime import date

FRAMES = {"science_uncertainty", "economic_cost",
          "consensus_acknowledgement", "policy_mandate",
          "other_or_undetermined"}
ARMS = {"GCC-linked-outlet", "comparison-outlet"}
PERIODS = {"before", "after"}
REQUIRED = {"id","source_sha256","outlet","date","treatment",
            "period","frame","coder_id","review_receipt","source_text_reviewed",
            "source_file"}

def wilson(success: int, n: int, z: float = 1.96) -> list[float]:
    if n <= 0:
        raise ValueError("Wilson interval requires observed denominator")
    p = success / n
    d = 1.0 + z*z/n
    center = (p + z*z/(2*n))/d
    half = z * sqrt(p*(1-p)/n + z*z/(4*n*n))/d
    return [round(max(0.0,center-half),6),round(min(1.0,center+half),6)]

def analyse(rows: list[dict], focus: str, intervention_date: str,
            intervention_receipt: str, source_root: Path | None = None,
            synthetic_fixture: bool = False) -> dict:
    if not intervention_receipt or intervention_receipt.startswith("UNVERIFIED"):
        raise ValueError("Source-specific intervention receipt required")
    if not synthetic_fixture and source_root is None:
        raise ValueError("Source root required for real source-byte verification")
    if not synthetic_fixture and "SYNTHETIC" in intervention_receipt.upper():
        raise ValueError("Synthetic intervention receipt cannot back a real study")
    if source_root is not None:
        source_root = source_root.resolve(strict=True)
        if not source_root.is_dir():
            raise ValueError("Source root must be an existing directory")
    try:
        cutoff = date.fromisoformat(intervention_date)
    except (ValueError, TypeError):
        raise ValueError("Invalid evidence-backed intervention date") from None
    if focus not in FRAMES - {"other_or_undetermined"}:
        raise ValueError("Invalid substantive frame")
    seen = set()
    seen_originals = set()
    outlet_arms = {}
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
        assigned_arm = outlet_arms.setdefault(row["outlet"], row["treatment"])
        if assigned_arm != row["treatment"]:
            raise ValueError("Same outlet assigned to both treatment and comparison arms")
        digest = row["source_sha256"]
        if not isinstance(digest,str) or len(digest)!=64 or any(
            c not in "0123456789abcdef" for c in digest):
            raise ValueError("Original document SHA256 required")
        if not synthetic_fixture:
            # Document identity is not the submitter's arbitrary row ID.
            # The same original byte stream cannot be counted twice,
            # including in different treatment or period cells.
            if digest in seen_originals:
                raise ValueError("Duplicate original bytes counted as separate articles")
            seen_originals.add(digest)
            if "SYNTHETIC" in str(row["review_receipt"]).upper():
                raise ValueError("Synthetic reviewer receipt not admissible")
            rel = Path(str(row["source_file"]))
            if rel.is_absolute() or ".." in rel.parts:
                raise ValueError("Source file must be relative and non-traversing")
            path = source_root.joinpath(rel)
            if path.is_symlink():
                raise ValueError("Symlink source files not accepted")
            checked_path = path.resolve(strict=True)
            if not checked_path.is_relative_to(source_root) or not checked_path.is_file():
                raise ValueError("Source file must belong to source root")
            real_digest = hashlib.sha256(checked_path.read_bytes()).hexdigest()
            if real_digest != digest:
                raise ValueError("Source bytes do not match supplied SHA-256")
        try:
            dt=date.fromisoformat(row["date"])
        except (ValueError,TypeError):
            raise ValueError("Invalid article date") from None
        if row["period"] == "before" and dt >= cutoff:
            raise ValueError("Before period not before documented intervention")
        if row["period"] == "after" and dt < cutoff:
            raise ValueError("After period precedes documented intervention")
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
            "source_bytes_verified":not synthetic_fixture,
            "focus":focus,"article_count":len(rows),
            "intervention_date":intervention_date,
            "intervention_receipt":intervention_receipt,
            "counts":counts,
            "descriptive_difference_in_differences":round(descriptive_did,6),
            "causal_attribution":"NOT_IDENTIFIED",
            "historical_original_authenticity_established":False,
            "limitations":["Sampling frame selection has not been validated by this code",
                           "The treatment contrast can be confounded by concurrent events",
                           "Article clustering/outlet dependence not addressed by Wilson intervals",
                           "The measured contrast does not estimate policy or audience persuasion"]}

def self_test() -> None:
    synthetic=[]
    for arm in sorted(ARMS):
        for period in sorted(PERIODS):
            for i in range(3):
                synthetic.append({
                    "id":f"synthetic-{arm}-{period}-{i}",
                    "source_file":f"synthetic-{arm}-{period}-{i}.txt",
                    "source_sha256":hashlib.sha256(
                        f"synthetic-{arm}-{period}-{i}".encode()).hexdigest(),
                    "outlet":f"SYNTHETIC {arm}","date":
                        "1992-05-01" if period=="before" else "1994-05-01",
                    "treatment":arm,"period":period,
                    "frame":"science_uncertainty" if i==0 or (
                        arm=="GCC-linked-outlet" and period=="after") else "other_or_undetermined",
                    "coder_id":"SYNTHETIC","review_receipt":"SYNTHETIC-NOT-ACTUAL",
                    "source_text_reviewed":True})
    result=analyse(synthetic,"science_uncertainty","1993-01-01","SYNTHETIC-NOT-ACTUAL", synthetic_fixture=True)
    assert result["article_count"]==12
    assert result["causal_attribution"]=="NOT_IDENTIFIED"
    assert result["descriptive_difference_in_differences"]==0.666667
    try:
        analyse(synthetic[:-3],"science_uncertainty","1993-01-01","SYNTHETIC-NOT-ACTUAL", synthetic_fixture=True)
    except ValueError:
        pass
    else:
        raise AssertionError("Missing comparison cell accepted")
    broken=[dict(x) for x in synthetic]
    broken[0]["review_receipt"]=None
    try:
        analyse(broken,"science_uncertainty","1993-01-01","SYNTHETIC-NOT-ACTUAL", synthetic_fixture=True)
    except ValueError:
        pass
    else:
        raise AssertionError("Unreviewed document admitted")
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        for row in synthetic:
            path = root / row["source_file"]
            path.write_bytes(row["id"].encode())
            row["review_receipt"] = "LOCAL-FIXTURE-REVIEW-ONLY"
        real_fixture = analyse(
            synthetic, "science_uncertainty", "1993-01-01",
            "LOCAL-FIXTURE-DATE-RECEIPT", source_root=root)
        assert real_fixture["source_bytes_verified"] is True
        damaged = [dict(r) for r in synthetic]
        damaged[0]["source_sha256"] = "0"*64
        try:
            analyse(damaged, "science_uncertainty", "1993-01-01",
                    "LOCAL-FIXTURE-DATE-RECEIPT", source_root=root)
        except ValueError:
            pass
        else:
            raise AssertionError("Mismatched source bytes incorrectly admitted")
        damaged = [dict(r) for r in synthetic]
        damaged[0]["source_file"] = "../escape.txt"
        try:
            analyse(damaged, "science_uncertainty", "1993-01-01",
                    "LOCAL-FIXTURE-DATE-RECEIPT", source_root=root)
        except ValueError:
            pass
        else:
            raise AssertionError("Traversing source path incorrectly admitted")
    # The same source may support several claims, but it cannot be
    # recounted as two independent original articles in a frame denominator.
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        for row in synthetic:
            (root / row["source_file"]).write_bytes(row["id"].encode())
        duplicate = [dict(x) for x in synthetic]
        duplicate[1]["source_sha256"] = duplicate[0]["source_sha256"]
        duplicate[1]["source_file"] = duplicate[0]["source_file"]
        try:
            analyse(duplicate, "science_uncertainty", "1993-01-01",
                    "LOCAL-FIXTURE-DATE-RECEIPT", source_root=root)
        except ValueError as e:
            assert "Duplicate original bytes" in str(e)
        else:
            raise AssertionError("Recounted original article was admitted")
        arms = [dict(x) for x in synthetic]
        # One outlet across both arms is a contaminated comparison.
        arms[0]["outlet"] = arms[-1]["outlet"]
        try:
            analyse(arms, "science_uncertainty", "1993-01-01",
                    "LOCAL-FIXTURE-DATE-RECEIPT", source_root=root)
        except ValueError as e:
            assert "both treatment and comparison arms" in str(e)
        else:
            raise AssertionError("Contradictory outlet arm accepted")
    print("PASS: synthetic 2x2 descriptives, Wilson limits, no-causality, missing-cell, review, digest and path guards")

def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input",type=Path)
    p.add_argument("--output",type=Path)
    p.add_argument("--focus",default="science_uncertainty")
    p.add_argument("--intervention-date",help="YYYY-MM-DD backed by original source")
    p.add_argument("--intervention-receipt",help="Source ID for actual intervention onset")
    p.add_argument("--source-root",type=Path,help="Original, locally preserved article-byte root")
    p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    if a.self_test:
        self_test()
        return
    if (a.input is None or a.output is None or
        not a.intervention_date or not a.intervention_receipt or
        a.source_root is None):
        p.error("--input --output --intervention-date and --intervention-receipt required")
    rows=[json.loads(line) for line in a.input.read_text(encoding="utf-8").splitlines() if line.strip()]
    result=analyse(rows,a.focus,a.intervention_date,a.intervention_receipt,
                   source_root=a.source_root)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n",encoding="utf-8")
    print(f"Wrote descriptive results for {result['article_count']} reviewed items; causal attribution NOT IDENTIFIED")

if __name__=="__main__":
    main()
