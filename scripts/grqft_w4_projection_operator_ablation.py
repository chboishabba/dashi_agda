#!/usr/bin/env python3
"""Ablate the W4 Z-window projection operator against the ratio-path denominator.

The accepted CMS t43 ratio and rejected W4 absolute observable share the
76--106 GeV denominator window but do not use exactly the same projection
operator.  This script compares:

  A. current W4 shape: predict_dirty_z_peak_shape / sigma_DASHI
  B. ratio-style denominator density: the same 5-point phi-star quadrature
     used internally by the t43 ratio path, evaluated only on 76--106 GeV

Both receive exactly one covariance-weighted overall scale against t21/t22.
No result is promoted; the comparison only localises projection-operator debt.
"""
from __future__ import annotations

import argparse, csv, json, math, sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0,str(ROOT))

from DASHI.Physics.Prediction import sigma_dashi as model

T21=ROOT/"scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv"
T22=ROOT/"scripts/data/hepdata/ins2079374_Covariance_phistar_mass_76-106_t22.csv"

def rows(path):
    return [r for r in csv.reader(
        line for line in path.read_text().splitlines()
        if line and not line.startswith("#")
    )]

def parse_data():
    rr=rows(T21)
    return [{"mid":float(x[0]),"low":float(x[1]),"high":float(x[2]),"y":float(x[3])} for x in rr[1:]]

def parse_cov(data):
    rr=rows(T22); n=len(data); C=[[0.0]*n for _ in range(n)]
    key={(d["mid"],d["low"],d["high"]):i for i,d in enumerate(data)}
    current=None; seen=0
    for r in rr:
        if len(r)!=7: continue
        if r[0]=="$\\varphi^*$":
            current=r[6]
            continue
        if current is None or not current.startswith("Total uncertainty"):
            continue
        a=tuple(map(float,r[:3])); b=tuple(map(float,r[3:6]))
        if a in key and b in key:
            C[key[a]][key[b]]=float(r[6]); seen+=1
    if seen!=n*n:
        raise RuntimeError(f"incomplete covariance: {seen} / {n*n}")
    return C

def solve(A,b):
    n=len(b); M=[A[i][:]+[b[i]] for i in range(n)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(M[r][c]))
        M[c],M[p]=M[p],M[c]
        q=M[c][c]
        if abs(q)<1e-30: raise ArithmeticError("singular covariance")
        for j in range(c,n+1): M[c][j]/=q
        for r in range(n):
            if r==c: continue
            f=M[r][c]
            for j in range(c,n+1): M[r][j]-=f*M[c][j]
    return [M[i][n] for i in range(n)]

def dot(a,b): return sum(x*y for x,y in zip(a,b))

def fit(shape,y,C):
    ci_y=solve(C,y); ci_s=solve(C,shape)
    scale=dot(shape,ci_y)/dot(shape,ci_s)
    pred=[scale*x for x in shape]
    resid=[p-d for p,d in zip(pred,y)]
    chi2=dot(resid,solve(C,resid))
    return {"scale":scale,"chi2":chi2,"dof":len(y)-1,"chi2PerDof":chi2/(len(y)-1),
            "firstPrediction":pred[0],"lastPrediction":pred[-1]}

def ratio_style_denominator_density(data):
    out=[]
    nodes=model.RATIO_BIN_INTEGRATION_NODES
    weights=model.RATIO_BIN_INTEGRATION_WEIGHTS
    loM,hiM=model.MASS_WINDOW_76_106_GEV
    for b in data:
        width=b["high"]-b["low"]
        total=0.0; wsum=0.0
        for node,weight in zip(nodes,weights):
            phi=0.5*(b["low"]+b["high"])+0.5*width*node
            total += weight*model._window_sigma_density_at_phi(
                loM,hiM,phi,b["low"],b["high"])
            wsum += weight
        out.append(total/wsum)
    return out

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",type=Path,default=ROOT/"outputs/grqft_w4_projection_operator_ablation.json")
    a=ap.parse_args()
    data=parse_data(); C=parse_cov(data); y=[d["y"] for d in data]
    bins=[{"phiStarLow":d["low"],"phiStarHigh":d["high"]} for d in data]
    raw=model.predict_dirty_z_peak_shape(bins)
    ratio_den=ratio_style_denominator_density(data)
    result={
      "artifactSchema":"dashi-grqft-w4-projection-operator-ablation-v1",
      "currentW4SigmaDashiShape":fit(raw,y,C),
      "ratioPathFivePointDenominatorDensity":fit(ratio_den,y,C),
      "sharedWindowGeV":[76,106],
      "comparison":"same underlying sigma_dashi construction; different phi-star projection operator",
      "posteriorDiagnosticRefinementInModelMetadata":model.metadata().get("posteriorDiagnosticRefinement"),
      "promotesW4":False,
      "interpretationBoundary":[
        "A lower chi2 for the ratio-style denominator would localise part of W4 failure to projection/operator mismatch.",
        "A similarly bad chi2 would push the defect upstream into the common absolute density/physics model.",
        "Neither outcome proves empirical adequacy or a unique physical mechanism."
      ]
    }
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
