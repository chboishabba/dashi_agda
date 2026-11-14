#!/usr/bin/env python3
"""Compare ORIGINAL Heinemeier human AMS rows against SAME-HEMISPHERE bomb curves.

Heinemeier et al. 2013 Table 1, DOI 10.1096/fj.12-225599: Arkansas donors
examined in 2000, pMC values and analytical sigma; original OL flags retained.
Hua et al. 2021/22, DOI 10.1017/RDC.2021.95: source 1950-2019 atmospheric
NH1, NH2, NH3 annual curves, redistributed under GPL >= 2 by rintcal.
Fetch the full original curves ONLY if they match pinned Git blob SHA-1.

This deliberately reports an *illustrative* lifetime envelope in 100*F14C
units. pMC vs F14C requires a source-consistent fractionation, date/decay,
measurement convention and dietary lag before a calibrated z score, turnover
parameter or nuclear residual. Missing pre-1950 years and 2000+ are not
extrapolated. Curves represent population/regional air, not diets/individuals.
"""
from __future__ import annotations
import argparse,csv,hashlib,json,math
from pathlib import Path
from urllib.request import urlopen

ROOT=Path(__file__).resolve().parents[1]
AMS=ROOT/"Artifacts/ksw668/heinemeier2013_original_human_ams_table1.csv"
SOURCE="https://raw.githubusercontent.com/Maarten14C/rintcal/master/inst/extdata/"
BLOBS={
  "NH1": "f7ff49b2ff6ed99f2a6b5aa811c86a774082cbcf",
  "NH2": "296b7fbbee8f69f87501be05f9b1a1391a49e0f5",
  "NH3": "aafd74536ec0690f1c1943ac98da3caf7972f59f",
}
CAVEAT=("Uncalibrated 100*F14C atmospheric envelope vs original human pMC "
        "measurements; pMC conversion, original decay normalization, dietary "
        "lags, local mixing, contamination and year boundaries remain open.")


def git_blob(raw):
    return hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()


def download_curve(zone:str, root:Path|None):
    filename="postbomb_"+zone+".14C"
    raw=(root/filename).read_bytes() if root is not None else \
       urlopen(SOURCE+filename,timeout=40).read()
    if git_blob(raw)!=BLOBS[zone]:
        raise ValueError(f"Refusing changed rintcal {zone} bytes: {git_blob(raw)}")
    data=[]
    for ln in raw.decode("utf-8").splitlines():
        if not ln.strip() or ln.lstrip().startswith("#"):continue
        cols=ln.split()
        if len(cols)!=3:raise ValueError("Bad original curve row")
        bp,rc,sigma=map(float,cols)
        if sigma<0:raise ValueError("Negative atmospheric error")
        factor=math.exp(-rc/8033)
        data.append({"year":1950-bp,"hundred_F14C":100*factor,
                     "hundred_F14C_sigma":100*factor*sigma/8033,
                     "source_age_BP":rc,"source_age_sd_BP":sigma})
    data.sort(key=lambda z:z["year"])
    if len(data)!=70 or data[0]["year"]!=1950.5 or data[-1]["year"]!=2019.5:
        raise ValueError("Source annual curve census changed")
    return data


def load_ams():
    with AMS.open(newline="",encoding="utf-8") as handle:
        rows=list(csv.DictReader(handle))
    if len(rows)!=34:raise ValueError("Original published AMS table changed")
    return rows


def age_lifetime_bounds(curve,birth,year_of_autopsy=2000):
    """Return envelope over sampled annual midpoints, never extrapolated."""
    usable=[p for p in curve if p["year"]>=max(birth,1950)
            and p["year"]<=year_of_autopsy]
    if not usable:
        raise ValueError("No atmospheric support during measured lifespan")
    return min(usable,key=lambda v:v["hundred_F14C"]),\
           max(usable,key=lambda v:v["hundred_F14C"])


def audit(rows,curves):
    exams=[]
    for r in rows:
        if r["tissue"]!="Tendon":continue
        obs=float(r["pMC"]);born=int(r["birth_year"])
        per_zone={}
        for z,curve in curves.items():
            low,high=age_lifetime_bounds(curve,born)
            excess=obs-high["hundred_F14C"]
            deficit=low["hundred_F14C"]-obs
            per_zone[z]={
                "min_hundred_F14C":round(low["hundred_F14C"],5),
                "max_hundred_F14C":round(high["hundred_F14C"],5),
                "below_min":round(max(0,deficit),5),
                "above_max":round(max(0,excess),5),
                "outside_envelope":deficit>0 or excess>0,
            }
        exams.append({
          "donor":r["sample_label"],"ams_id":r["ams_id"],
          "birth_year":born,"observed_pMC":obs,
          "source_analytical_sigma_pMC":float(r["pMC_sigma"]),
          "source_outlier_flag":r["source_outlier"]=="true",
          "regional_lifetime_illustrative_bounds":per_zone,
        })
    author_outliers=[r for r in exams if r["source_outlier_flag"]]
    expected={"15882.1","15882.2","16252","15883","16247"}
    if {r["ams_id"] for r in author_outliers}!=expected:
        raise ValueError("Original author outlier assays changed")
    for r in author_outliers:
        if not all(v["outside_envelope"] for v in
                   r["regional_lifetime_illustrative_bounds"].values()):
            raise ValueError("Original outlier no longer outside all zonal envelopes: "+r["ams_id"])
    return {
      "schema":"dashi.ksw668.human-NH-AMS-atmospheric-screen.v1",
      "attribution":{"human":"Heinemeier et al. FASEB 2013, DOI 10.1096/fj.12-225599",
                     "atmosphere":"Hua et al. Radiocarbon 2022, DOI 10.1017/RDC.2021.95",
                     "licensed_distribution":"Maarten14C/rintcal, GPL >=2"},
      "rintcal_git_blobs":BLOBS,
      "human_AMS_assays_screened":len(exams),
      "author_outlier_assays":len(author_outliers),
      "author_outlier_donors":["25","28","30"],
      "all_author_outlier_assays_outside_all_three_simple_envelopes":True,
      "outlier_screen":author_outliers,
      "status":"source-derived quantitative SCREEN; NOT calibrated isotopic residual/causal proof",
      "limitations":CAVEAT,
    }


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--curve-dir",type=Path,
                    help="Offline source curves postbomb_NH{1,2,3}.14C; original blobs")
    ap.add_argument("--receipt",type=Path)
    args=ap.parse_args()
    curves={zone:download_curve(zone,args.curve_dir) for zone in BLOBS}
    result=audit(load_ams(),curves)
    txt=json.dumps(result,sort_keys=True,indent=2)+"\n"
    if args.receipt:args.receipt.write_text(txt,encoding="utf-8")
    print(txt)


if __name__=="__main__":
    main()
