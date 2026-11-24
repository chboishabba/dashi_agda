#!/usr/bin/env python3
"""Join existing signed MMV31 outer and inner packets; conditional modular witness."""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
from monster3b_actual_projective_sym2_intertwiner import inverse, symmetric_square

P = 31

def scalar(M):
    n = len(M)
    a = int(M[0, 0]) % P
    if not a or not np.array_equal(M % P, a*np.eye(n,dtype=np.int64)):
        raise ValueError("zero or nonscalar residual")
    return a

def join(A,H,F):
    for s in (1,2):
        for M,n in ((A[s],12),(H[s],78),(F[s],78)):
            if M.shape != (n,n):
                raise ValueError("wrong signed block shape")
            inverse(M)
    beta = {}
    lam = {}
    Q = {}
    for s,t in ((1,2),(2,1)):
        beta[s] = scalar(H[t]@H[s]%P)
        if scalar(-A[t]@A[s]%P) != beta[s]:
            raise ValueError("12/78 projective square disagreement")
        Q[s] = symmetric_square(inverse(A[s]).T)
        lam[s] = scalar(F[t]@H[s]%P@inverse(F[s])%P@inverse(Q[s])%P)
    if beta[1]!=beta[2] or lam[1]*lam[2]%P!=pow(beta[1],3,P):
        raise ValueError("signed cubic product obstruction")
    # Relative normalization fixes the first square without erasing the
    # projective square scalar. Reverse residual is then beta cubed.
    G={1:F[1],2:F[2]*pow(lam[1],-1,P)%P}
    for s,t,k in ((1,2,1),(2,1,pow(beta[1],3,P))):
        if not np.array_equal(G[t]@H[s]%P,k*(Q[s]@G[s]%P)%P):
            raise ValueError("reverse normalized square failed")
    return G,{"beta":beta,"lambda":lam,"relative_normalized_reverse":pow(beta[1],3,P)}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--inner",type=Path,required=True)
    p.add_argument("--outer",type=Path,required=True)
    p.add_argument("--outdir",type=Path,required=True)
    a=p.parse_args()
    a.outdir.mkdir(parents=True,exist_ok=True)
    hashes={}
    def read(path):
        hashes[str(path)]=hashlib.sha256(path.read_bytes()).hexdigest()
        return np.load(path,allow_pickle=False)
    report={"actual_char0":False,"source_provenance_independently_authenticated":False}
    try:
        A={};H={};F={};S={};T={}
        for s,direction in ((1,"plus_to_minus"),(2,"minus_to_plus")):
            with read(a.inner/f"actual_MM_projective_Sym2_78_intertwiner_phase{s}.npz") as f:
                F[s]=f["transport78"].astype(np.int64)%P
                S[s]={g:f["actual_B78_"+g].astype(np.int64)%P for g in ("D","E")}
                T[s]={g:f["derived_Sym2_"+g].astype(np.int64)%P for g in ("D","E")}
            for n,target in ((12,A),(78,H)):
                with read(a.outer/f"actual_MM31_C_{direction}_eig{n}.npz") as f:
                    target[s]=f["matrix"].astype(np.int64)%P
            for g in ("D","E"):
                if not np.array_equal(F[s]@S[s][g]%P,T[s][g]@F[s]%P):
                    raise ValueError("inner packet equation failed")
        G,res=join(A,H,F)
        for s in (1,2):
            for g in ("D","E"):
                if not np.array_equal(G[s]@S[s][g]%P,T[s][g]@G[s]%P):
                    raise ValueError("relative gauge broke inner equation")
        np.savez_compressed(a.outdir/"signed_outer_transport.npz",Fplus=G[1],Fminus=G[2])
        report.update(status="CONDITIONAL_MODULAR_PACKET_SQUARES_MATCH",**res)
    except Exception as exc:
        report.update(status="BLOCKED_OR_RESIDUAL",error=repr(exc))
    report["input_sha256"]=hashes
    (a.outdir/"signed_outer_report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report))
    return 0 if report["status"]=="CONDITIONAL_MODULAR_PACKET_SQUARES_MATCH" else 2

if __name__=="__main__":
    raise SystemExit(main())
