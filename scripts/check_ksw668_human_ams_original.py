#!/usr/bin/env python3
"""Source-author human 14C AMS sample audit; never deduplicate assay rows silently.

Original Heinemeier et al. 2013 FASEB J DOI 10.1096/fj.12-225599 Table 1.
Source cell: donor, original AMS ID, tissue, year of birth, pMC and error.
These are original tissue observations; no emotion intervention or endogenous
nuclear conversion measured. This is not paired longitudinal time series.
"""
import argparse,csv,hashlib,json,math
from collections import Counter,defaultdict
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
DEFAULT=ROOT/"Artifacts/ksw668/heinemeier2013_original_human_ams_table1.csv"
DOI="10.1096/fj.12-225599"


def inspect(path):
    path=Path(path)
    raw=path.read_bytes()
    rows=list(csv.DictReader(raw.decode("utf-8").splitlines()))
    assert len(rows)==34, "Original Table 1 assay row count has changed"
    assert len({r["sample_label"] for r in rows})==28, "Donor count has changed"
    assert Counter(r["tissue"] for r in rows)=={"Tendon":30,"Muscle":4}
    assert len([r for r in rows if r["source_outlier"]=="true"])==5
    assert all(r["source_doi"]==DOI for r in rows)
    assert len({r["ams_id"] for r in rows})==34, "Do not collapse repeated original AMS assays"
    donors=defaultdict(list)
    for r in rows:
        for k in ("pMC","pMC_sigma"):
            v=float(r[k])
            if not math.isfinite(v) or v<=0: raise ValueError("Bad source observation")
        if r["source_outlier"] not in ("true","false"):
            raise ValueError("Unknown original author outlier flag")
        donors[r["sample_label"]].append(r)
    paired=[]
    for label in sorted(donors):
        rs=donors[label]
        t=[r for r in rs if r["tissue"]=="Tendon"]
        m=[r for r in rs if r["tissue"]=="Muscle"]
        if t and m:
            if len(m)!=1: raise ValueError("Unexpected muscle duplicates")
            if len(t)==1 and all(r["source_outlier"]=="false" for r in t+m):
                delta=float(t[0]["pMC"])-float(m[0]["pMC"])
                # Analytical measurement error only; no calibration/batch covariance.
                propagated=math.hypot(float(t[0]["pMC_sigma"]),float(m[0]["pMC_sigma"]))
                paired.append(dict(donor_ref=label,tendon_ams=t[0]["ams_id"],
                                   muscle_ams=m[0]["ams_id"],
                                   diff_pMC=round(delta,5),
                                   analytical_sigma_pMC=round(propagated,5),
                                   same_donor=True,source_outliers=False))
            else:
                paired.append(dict(donor_ref=label,
                                   source_outliers=True,
                                   multiple_tendon_assays=len(t),
                                   reason="Excluded from simple paired contrast; preserve original rows"))
    eligible=[p for p in paired if not p["source_outliers"]]
    assert sorted(p["donor_ref"] for p in eligible)==["24","26"]
    assert len(paired)==4
    assert eligible[0]["diff_pMC"]==25.75
    assert eligible[1]["diff_pMC"]==38.69
    return {
      "schema":"dashi.ksw668.human-AMS-source-replay.v1",
      "source_doi":DOI,
      "raw_table_extract_sha256":hashlib.sha256(raw).hexdigest(),
      "assays":len(rows),"distinct_donors":len(donors),
      "tendon_assays":30,"muscle_assays":4,
      "source_flagged_outlier_assays":5,
      "source_original_table":"Wiley FASEB J 2013 Table 1, sourced in repo CSV",
      "same_donor_tissue_comparisons":paired,
      "units":"pMC (percent modern carbon); NOT isotope fraction F14C without conventions",
      "statistical_scope":"analytical error only; donor selection, dietary lag, geomagnetic background and assay batch/covariance unmodelled",
      "no_inference":"no measured induced nuclear conversion or emotional intervention",
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--original-table",type=Path,default=DEFAULT)
    p.add_argument("--out",type=Path)
    args=p.parse_args()
    r=inspect(args.original_table)
    s=json.dumps(r,sort_keys=True,indent=2)+"\n"
    if args.out:args.out.write_text(s,encoding="utf-8")
    print(s)


if __name__=="__main__":
    main()
