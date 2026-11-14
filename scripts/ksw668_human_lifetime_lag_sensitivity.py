#!/usr/bin/env python3
"""KSW E1: measured human AMS vs NH1/NH2/NH3 atmosphere, lag-window test.

The original ksw668_human_atmospheric_lifetime.py fetches, source-blobs
checks and parses all 70 yearly Hua et al. 14C atmospheric rows for each
Northern Hemisphere zone. This program checks 30 original Heinemeier et al.
2013 tendon AMS pMC values, retaining all 5 source-author OL outlier flags.

At each lag L in 0,1,2,5 years, allow possible atmospheric source years
from (human birth year - L) through (2000 original source autopsy year + L).
This is a SUPERSIZED temporal envelope stress test, not an
actual donor dietary-history model or isotope convention calibration.
The reported pMC vs 100*F14C differences are thus comparisons of numerical
proxies ONLY, not nuclear residuals or experimental significance.
"""
import argparse,json
from pathlib import Path
import ksw668_human_atmospheric_lifetime as Source

LAGS=(0,1,2,5)
EXPECTED_FLAGGED={"15882.1","15882.2","16252","15883","16247"}


def analyze(curves,rows):
    tendon=[r for r in rows if r["tissue"]=="Tendon"]
    if len(tendon)!=30:raise AssertionError("Changed original human source assay census")
    result={}
    for lag in LAGS:
        assays=[]
        for r in tendon:
            birth=int(r["birth_year"])
            obs=float(r["pMC"])
            zones={}
            for name,curve in curves.items():
                included=[z for z in curve
                          if z["year"]>=birth-lag and z["year"]<=2000+lag]
                if not included:raise ValueError("No source atmosphere during plausible lifetime")
                mini=min(z["hundred_F14C"] for z in included)
                maxi=max(z["hundred_F14C"] for z in included)
                zones[name]={
                   "outside_uncalibrated_envelope":bool(obs<mini or obs>maxi),
                   "below_numeric_proxy":round(max(0,mini-obs),6),
                   "above_numeric_proxy":round(max(0,obs-maxi),6),
                   "source_min_100F14C":round(mini,6),
                   "source_max_100F14C":round(maxi,6),
                }
            assays.append({
                "donor":r["sample_label"],"original_AMS_ID":r["ams_id"],
                "original_author_outlier":r["source_outlier"]=="true",
                "original_observed_pMC":obs,
                "regions":zones,
                "outside_every_NH_zone":all(x["outside_uncalibrated_envelope"]
                                             for x in zones.values())
            })
        outside=[a for a in assays if a["outside_every_NH_zone"]]
        if set(a["original_AMS_ID"] for a in outside)!=EXPECTED_FLAGGED:
            raise AssertionError("Original outlier source/lag conclusion changed: "+str(lag))
        result[str(lag)]={
           "years_extended_at_both_lifetime_ends":lag,
           "original_author_outlier_assays_outside_all_zones":sum(a[
               "original_author_outlier"] and a["outside_every_NH_zone"] for a in assays),
           "source_non_outlier_assays_outside_any_zone":sum(
               not a["original_author_outlier"] and any(
                 x["outside_uncalibrated_envelope"] for x in a["regions"].values())
                for a in assays),
           "original_outliers":[a for a in assays if a["original_author_outlier"]]
        }
    return {
       "schema":"dashi.ksw668.original-human-atmosphere-lag-sensitivity.v1",
       "source_papers":["10.1096/fj.12-225599","10.1017/RDC.2021.95"],
       "rintcal_git_blobs":Source.BLOBS,
       "original_tendon_AMS_assays":len(tendon),
       "timing_model":"deliberate interval stress-test, NOT a calibrated dietary-carbon lag model",
       "results_by_lag_years":result,
       "no_nuclear_production_inferred":True,
       "unresolved":"pMC/F14C normalization, donor food sourcing, residence/identity, AMS covariance, within-human controlled intervention"
    }


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--curve-dir",type=Path)
    ap.add_argument("--out",type=Path)
    ns=ap.parse_args()
    curves={name:Source.download_curve(name,ns.curve_dir) for name in Source.BLOBS}
    r=analyze(curves,Source.load_ams())
    txt=json.dumps(r,indent=2,sort_keys=True)+"\n"
    if ns.out:ns.out.write_text(txt)
    print(txt)


if __name__=="__main__":
    main()
