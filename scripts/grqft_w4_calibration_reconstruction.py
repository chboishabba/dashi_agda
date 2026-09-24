#!/usr/bin/env python3
"""Reconstruct the W4 Z-peak failure mechanism from committed repo objects.

Non-promoting diagnostic.  It compares:
  1. the current sigma_dashi dirty-Z shape;
  2. the naive bin-width reinterpretation;
  3. the fresh mass-general predictor;
and imports the already-committed residual-decomposition diagnostics.

No observed value is fed into either predictor.  The single scalar amplitude is
fit only by the same covariance-weighted least-squares diagnostic used by W4.
"""

from __future__ import annotations
import csv, importlib, json, math
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
T21=ROOT/"scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv"
T22=ROOT/"scripts/data/hepdata/ins2079374_Covariance_phistar_mass_76-106_t22.csv"
DECOMP=ROOT/"scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json"
OLD=ROOT/"logs/research/w4_z_peak_anchor_dirty_run_20260513.json"
OUT=ROOT/"outputs/grqft_w4_calibration_reconstruction.json"

def noncomment(path):
    return [line for line in path.read_text().splitlines() if line and not line.startswith("#")]

def load_data():
    rows=list(csv.reader(noncomment(T21)))
    return [
        {"phi":float(r[0]),"lo":float(r[1]),"hi":float(r[2]),"data":float(r[3])}
        for r in rows[1:]
    ]

def load_cov(data):
    rows=list(csv.reader(noncomment(T22)))
    key={(d["phi"],d["lo"],d["hi"]):i for i,d in enumerate(data)}
    n=len(data); cov=[[0.0]*n for _ in range(n)]
    seen=0
    for r in rows[1:]:
        if r[0] == "$\\varphi^*$":
            if seen: break
            continue
        if len(r)!=7: continue
        a=tuple(map(float,r[:3])); b=tuple(map(float,r[3:6]))
        if a in key and b in key:
            cov[key[a]][key[b]]=float(r[6]); seen+=1
            if seen==n*n: break
    if seen != n*n: raise RuntimeError(f"expected {n*n} covariance entries, got {seen}")
    return cov

def solve(a,b):
    n=len(b); m=[row[:] + [b[i]] for i,row in enumerate(a)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(m[r][c]))
        m[c],m[p]=m[p],m[c]
        q=m[c][c]
        if abs(q)<1e-30: raise ArithmeticError("singular covariance")
        for j in range(c,n+1): m[c][j]/=q
        for r in range(n):
            if r==c: continue
            f=m[r][c]
            for j in range(c,n+1): m[r][j]-=f*m[c][j]
    return [m[i][n] for i in range(n)]

def dot(a,b): return sum(x*y for x,y in zip(a,b))

def fit(shape,data,cov):
    y=[d["data"] for d in data]
    ci_y=solve(cov,y); ci_s=solve(cov,shape)
    amp=dot(shape,ci_y)/dot(shape,ci_s)
    pred=[amp*x for x in shape]
    residual=[p-v for p,v in zip(pred,y)]
    chi2=dot(residual,solve(cov,residual))
    dof=len(y)-1
    pulls=[residual[i]/math.sqrt(cov[i][i]) for i in range(len(y))]
    return {
        "scale":amp,"chi2":chi2,"dof":dof,"chi2PerDof":chi2/dof,
        "firstPrediction":pred[0],"lastPrediction":pred[-1],
        "firstPull":pulls[0],"lastPull":pulls[-1],
        "endpointShapeRatio":shape[0]/shape[-1],
    }

def main():
    data=load_data(); cov=load_cov(data)
    bins=[{"phiStar":d["phi"],"phiStarLow":d["lo"],"phiStarHigh":d["hi"]} for d in data]
    current=importlib.import_module("DASHI.Physics.Prediction.sigma_dashi")
    mass=importlib.import_module("DASHI.Physics.Prediction.sigma_dashi_mass_general")
    current_shape=current.predict_dirty_z_peak_shape(bins)
    width_shape=[v/(d["hi"]-d["lo"]) for v,d in zip(current_shape,data)]
    mass_shape=[mass.sigma_DASHI_mass_general(76.0,106.0,d["lo"],d["hi"]) for d in data]
    old=json.loads(OLD.read_text())
    dec=json.loads(DECOMP.read_text())
    ext=dec["extended_basis_decomposition"]
    result={
      "artifactSchema":"dashi-grqft-w4-calibration-reconstruction-v1",
      "dataEndpointRatio":data[0]["data"]/data[-1]["data"],
      "currentCommittedRun":{
        "chi2":old["calibration"]["chi2"],
        "chi2PerDof":old["calibration"]["chi2PerDof"],
        "scale":old["calibration"]["scale"],
      },
      "currentShapeRefit":fit(current_shape,data,cov),
      "binWidthReinterpretation":fit(width_shape,data,cov),
      "massGeneralFreshCandidate":fit(mass_shape,data,cov),
      "residualMechanism":{
        "logLinearCoverage":ext["log_linear"]["coverage"],
        "logLinearResidualChi2PerDof":ext["log_linear"]["chi2_perp_per_dof"],
        "logCubicCoverage":ext["log_cubic"]["coverage"],
        "logCubicResidualChi2PerDof":ext["log_cubic"]["chi2_perp_per_dof"],
        "cssProxyCoverage":ext["css_resummation_basis"]["residual_projection"]["coverage"],
        "cssProxyResidualChi2PerDof":ext["css_resummation_basis"]["residual_projection"]["chi2_perp_per_dof"],
        "transition1PhiStar":ext["multi_transition_discrimination"]["transition_1_phi_star"],
        "transition2PhiStar":ext["multi_transition_discrimination"]["transition_2_phi_star"],
      },
      "diagnosis":[
        "current finite-carrier W4 shape is much too flat across phi-star",
        "naive bin-width reinterpretation does not repair the covariance-weighted failure",
        "fresh mass-general candidate is even flatter and is not a viable replacement",
        "dominant discrepancy is smooth shape structure, not one missing global normalization",
        "next physical candidate must add genuine low-phi resummation/nonperturbative structure, fiducial acceptance, and fixed-order tail before authority/promotion",
      ],
      "promotesW4":False,
    }
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=="__main__": main()
