#!/usr/bin/env python3
"""Replay the ratio-vs-absolute Drell--Yan contrast from committed artifacts.

This is a diagnostic localization receipt.  It does not infer a unique cause.
It only establishes that a bounded ratio observable has a much lower
covariance chi2/dof than the current absolute Z-window shape projection.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
W3=ROOT/"logs/research/w3_frozen_3205d74_t43_comparison_20260513.json"
W4=ROOT/"outputs/grqft_w4_calibration_reconstruction.json"
OUT=ROOT/"outputs/grqft_dy_ratio_absolute_localization.json"

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",type=Path,default=OUT)
    a=ap.parse_args()
    w3=json.loads(W3.read_text())
    w4=json.loads(W4.read_text())
    ratio=float(w3["comparison"]["chi2PerDof"])
    absolute=float(w4["currentShapeRefit"]["chi2PerDof"])
    result={
      "artifactSchema":"dashi-grqft-dy-ratio-absolute-localization-v1",
      "ratioObservable":{
        "scope":"CMS-SMP-20-003 t43 50--76 / 76--106 GeV phi-star ratio",
        "covariance":"t44 Total uncertainty",
        "chi2PerDof":ratio,
        "dof":w3["comparison"]["dof"],
        "meanPredData":w3["comparison"]["meanPredData"],
        "status":w3["comparison"]["status"],
      },
      "absoluteObservable":{
        "scope":"CMS-SMP-20-003 76--106 GeV absolute d-sigma/d-phi-star",
        "chi2PerDof":absolute,
        "dof":w4["currentShapeRefit"]["dof"],
        "status":"rejected-current-W4-projection",
      },
      "chi2PerDofContrastAbsoluteOverRatio":absolute/ratio,
      "inference":{
        "sharedCarrierGloballyRejected":False,
        "projectionSpecificDefectSearchPreferred":True,
        "uniqueCauseProved":False,
        "priorityTargets":[
          "absolute observable/Jacobian construction",
          "fiducial acceptance",
          "soft-recoil/TMD resummation",
          "nonperturbative transverse momentum",
          "fixed-order tail",
          "physical normalization after shape adequacy",
        ],
      },
      "atlasCovarianceChi2ReceiptUsed":False,
      "atlasBoundary":"No comparable low-chi2 ATLAS covariance receipt was found on current master; do not manufacture one from tail/projection diagnostics.",
      "promotesW4":False,
    }
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
