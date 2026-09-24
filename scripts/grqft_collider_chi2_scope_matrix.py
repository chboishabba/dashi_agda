#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
CMS=ROOT/"logs/research/w3_frozen_3205d74_t43_comparison_20260513.json"
ATLAS=ROOT/"outputs/sm_higgs_covariant_comparison/sm_higgs_covariant_comparison_summary.json"
ATLAS_ROWS=ROOT/"outputs/sm_higgs_covariant_comparison/sm_higgs_covariant_comparison_rows.json"
W4=ROOT/"outputs/grqft_w4_calibration_reconstruction.json"

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",type=Path,default=ROOT/"outputs/grqft_collider_chi2_scope_matrix.json")
    a=ap.parse_args()
    cms=json.loads(CMS.read_text())
    atlas=json.loads(ATLAS.read_text())
    rows=json.loads(ATLAS_ROWS.read_text())["comparison_rows"]
    w4=json.loads(W4.read_text())
    best=min(rows,key=lambda r:r["reduced_chi2"])
    result={
      "artifactSchema":"dashi-grqft-collider-chi2-scope-matrix-v1",
      "rows":[
        {
          "experiment":"CMS",
          "observable":"SMP-20-003 t43 50--76 / 76--106 phi-star ratio",
          "chi2PerDof":cms["comparison"]["chi2PerDof"],
          "dof":cms["comparison"]["dof"],
          "authority":"bounded-comparison-law-receipt",
          "promotion":"W3-bounded-only",
        },
        {
          "experiment":"ATLAS",
          "observable":best["observable_key"],
          "chi2PerDof":best["reduced_chi2"],
          "dof":best["dof"],
          "authority":best["authority_status"],
          "promotion":"none",
        },
        {
          "experiment":"CMS",
          "observable":"SMP-20-003 76--106 absolute d-sigma/d-phi-star current W4 projection",
          "chi2PerDof":w4["currentShapeRefit"]["chi2PerDof"],
          "dof":w4["currentShapeRefit"]["dof"],
          "authority":"rejected-projection-diagnostic",
          "promotion":"none",
        },
      ],
      "guards":{
        "compareOnlyWithScopeAndAuthority":True,
        "atlasFixtureCountsAsAcceptedValidation":False,
        "w4RejectionCancelsCMSRatioContact":False,
      },
      "atlasSummaryPromotionDecision":atlas["promotion_decision"],
    }
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=="__main__": main()
