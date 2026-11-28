"""Polar Ritz localization sweep on original repaired TOV (fixed conformal metric).

Does not presuppose positivity. The existing Ritz routine owns original
constitutive Hessian, exact Schwarzschild DtN, and constraint solve.
Finite subspaces are not a proof of full coercivity or free-boundary stability.
"""
import argparse
import json
import numpy as np
from scipy.linalg import eigh
from check_tov_polar_ritz_search import run

SUPPORTS={
    "centre":(.02,.28),
    "interior":(.15,.85),
    "surface":(.72,.98),
}
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--n",type=int,default=64)
    p.add_argument("--degree",type=int,default=2)
    p.add_argument("--ells",type=int,nargs="+",default=[1,2])
    args=p.parse_args()
    assert args.n>=16 and args.degree>=1 and all(l>=1 for l in args.ells)
    records=[]
    for name,annulus in SUPPORTS.items():
        for ell in args.ells:
            h,m=run(args.n,ell,args.degree,annulus)
            eigen=eigh(h,m,eigvals_only=True)
            row={"support":name,"annulus":annulus,"ell":ell,"n":args.n,
                 "degree":args.degree,"min_displacement_rayleigh":float(eigen[0]),
                 "min_coefficient_eigen":float(np.linalg.eigvalsh(h)[0]),
                 "negative_directions":int(np.count_nonzero(eigen<0))}
            assert np.isfinite(eigen).all()
            records.append(row)
            print("LOCALIZATION",json.dumps(row,sort_keys=True),flush=True)
    print("LOCALIZATION SUMMARY",json.dumps({
        "cases":len(records),
        "negative_cases":sum(z["negative_directions"]>0 for z in records),
        "minimum_rayleigh":min(z["min_displacement_rayleigh"] for z in records),
        "scope":"fixed conformal background and compactly supported material displacements only"
    },sort_keys=True),flush=True)
if __name__=="__main__":main()
