#!/usr/bin/env python3
"""Score an independent physical W4 phi-star prediction against frozen t21/t22.

Provider JSON must carry the exact 18 bin edges and absolute d sigma/d phi*
prediction values.  The nominal score uses NO fitted normalization.  A one-scale
refit is emitted only as a diagnostic to distinguish shape from normalization.
"""
from __future__ import annotations
import argparse,csv,json,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
T21=ROOT/"scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv"
T22=ROOT/"scripts/data/hepdata/ins2079374_Covariance_phistar_mass_76-106_t22.csv"
ALLOWED={"MiNNLO_PS","GENEVA_qT","ARTEMIDE","CASCADE_PB","DYTURBO","independent_TMD_or_resummed"}

def noncomment(p): return [x for x in p.read_text().splitlines() if x and not x.startswith("#")]
def data_rows():
    r=list(csv.reader(noncomment(T21)))
    return [{"mid":float(x[0]),"lo":float(x[1]),"hi":float(x[2]),"y":float(x[3])} for x in r[1:]]
def covariance(data):
    rows=list(csv.reader(noncomment(T22))); n=len(data); C=[[0.0]*n for _ in range(n)]
    key={(d["mid"],d["lo"],d["hi"]):i for i,d in enumerate(data)}; seen=0
    for r in rows[1:]:
        if r[0]=="$\\varphi^*$":
            if seen: break
            continue
        if len(r)!=7: continue
        a=tuple(map(float,r[:3])); b=tuple(map(float,r[3:6]))
        if a in key and b in key:
            C[key[a]][key[b]]=float(r[6]); seen+=1
            if seen==n*n: break
    if seen!=n*n: raise RuntimeError("incomplete covariance")
    return C
def solve(A,b):
    n=len(b); m=[r[:] + [b[i]] for i,r in enumerate(A)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(m[r][c])); m[c],m[p]=m[p],m[c]
        q=m[c][c]
        if abs(q)<1e-30: raise ArithmeticError("singular covariance")
        for j in range(c,n+1): m[c][j]/=q
        for r in range(n):
            if r==c: continue
            f=m[r][c]
            for j in range(c,n+1): m[r][j]-=f*m[c][j]
    return [r[n] for r in m]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def chi2(pred,y,C):
    r=[a-b for a,b in zip(pred,y)]
    return dot(r,solve(C,r))
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--provider",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    a=ap.parse_args()
    provider=json.loads(a.provider.read_text())
    model=provider.get("modelFamily")
    if model not in ALLOWED: raise ValueError(f"unsupported/undeclared physical model family: {model}")
    if provider.get("independentOfT21Fit") is not True: raise ValueError("provider must attest independentOfT21Fit=true")
    if provider.get("observable")!="d sigma/d phiStar": raise ValueError("wrong observable")
    if provider.get("unit")!="pb": raise ValueError("wrong unit")
    if provider.get("massWindowGeV")!=[76,106]: raise ValueError("wrong mass window")
    data=data_rows(); bins=provider["bins"]
    if len(bins)!=len(data): raise ValueError("wrong bin count")
    for b,d in zip(bins,data):
        if [float(b["low"]),float(b["high"])] != [d["lo"],d["hi"]]:
            raise ValueError("provider bin edges do not match frozen t21")
    pred=[float(b["prediction"]) for b in bins]; y=[d["y"] for d in data]; C=covariance(data)
    nominal=chi2(pred,y,C)
    ci_y=solve(C,y); ci_p=solve(C,pred); scale=dot(pred,ci_y)/dot(pred,ci_p)
    scaled=[scale*x for x in pred]; shape=chi2(scaled,y,C)
    out={
      "artifactSchema":"dashi-grqft-w4-independent-physical-prediction-v1",
      "modelFamily":model,"source":provider.get("source"),"independentOfT21Fit":True,
      "nominal":{"chi2":nominal,"dof":len(y),"chi2PerDof":nominal/len(y)},
      "shapeDiagnostic":{"bestFitScale":scale,"chi2":shape,"dof":len(y)-1,"chi2PerDof":shape/(len(y)-1)},
      "adequacyPromoted":False,
      "boundary":"scoring an independent physical prediction does not create DY/Candidate256 authority"
    }
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=="__main__": main()
