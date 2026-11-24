#!/usr/bin/env python3
"""Global scalar-free signed Weil section via the 365/364 parity determinant.

Uses the existing TOE kernel and literal zero-affine quotient chart.
One fixed cyclotomic embedding is used because compile_shape already
inserts the source/target phase. Model only: no MMV or ordinary Hom data.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
from itertools import product
import numpy as np
from monster3b_original729_weil_source_cocycle_weld import (
    model, parse_cover, power, DELTA, ROOTS, pack, I12, f3_pow)
from toe_cyclotomic_operator import columns

P=31
Z=5

def eval_fixed(q):
    def red(x):
        x=Fraction(x)
        return x.numerator*pow(x.denominator,-1,P)%P
    return (red(q[0])+Z*red(q[1]))%P

def det(A):
    A=np.asarray(A,dtype=np.int64).copy()%P
    d=1
    for j in range(len(A)):
        inds=np.flatnonzero(A[j:,j])
        if not len(inds):return 0
        i=j+int(inds[0])
        if i!=j:
            A[[i,j]]=A[[j,i]]
            d=-d
        a=int(A[j,j])
        d=d*a%P
        A[j+1:,j:]=(A[j+1:,j:]-((A[j+1:,j]*pow(a,-1,P))%P)[:,None]*A[j,j:])%P
    return d%P

def parity_index(n):
    X=np.asarray(list(product(range(3),repeat=n)),dtype=np.int64)
    return (-X%3)@3**np.arange(n-1,-1,-1)

def ratio(K,neg):
    K=np.asarray(K,dtype=np.int64)%P
    if not np.array_equal(K[neg,:],K[:,neg]):
        raise ValueError("model fails parity preservation")
    reps=np.flatnonzero(np.arange(len(neg))<neg)
    pos=np.r_[0,reps]
    even=K[np.ix_(pos,pos)].copy()
    even[:,1:]=(even[:,1:]+K[np.ix_(pos,neg[reps])])%P
    odd=(K[np.ix_(reps,reps)]-K[np.ix_(reps,neg[reps])])%P
    a,b=det(even),det(odd)
    if not a or not b:raise ValueError("singular parity block")
    return a*pow(b,-1,P)%P

def canonical(A,lam,s):
    R=model(A,lam,s)
    R["scalar"]=[1,0,1]
    n=len(R["origin"])
    N=3**n
    K=np.zeros((N,N),dtype=np.int64)
    scale=eval_fixed(power(DELTA,-R["rank"]))
    for j,y,(a,b) in columns(R):
        K[y,j]=np.asarray((a+Z*b)%P,dtype=np.int64)*scale%P
    neg=parity_index(n)
    d=ratio(K,neg)
    roots=[tuple(sign*x for x in root) for sign in (1,-1) for root in ROOTS]
    lifts=[q for q in roots if eval_fixed(q)==d]
    # Unitary determinants in Z[zeta,1/3] have norm 1 and are mu6
    # because 3 is ramified. F31 is injective on mu6.
    if len(lifts)!=1:raise ValueError("determinant ratio not in mu6")
    H=K*pow(d,-1,P)%P
    if ratio(H,neg)!=1:raise AssertionError("canonical determinant ratio")
    return H,{"det_ratio_Qzeta3":pack(lifts[0]),"det_ratio_mod31":d,
              "normalized_vacuum_mod31":int(H[0,0]),"rank":R["rank"]}

def replay(C,D):
    I=np.eye(729,dtype=np.int64)
    J=I[:,parity_index(6)]
    ops={};records={}
    for s in (1,2):
        for g,A,l in (("C",C,2),("D",D,1)):
            ops[g,s],records[g,s]=canonical(A,l,s)
    def word(w,s):
        # left action: rightmost literal generator acts first
        M=I.copy()
        for g in reversed(w):
            if g=="c":
                for h in "CCC":
                    M=ops[h,s]@M%P;s=3-s
            elif g=="d":
                for h in "DD":M=ops[h,s]@M%P
            else:
                M=ops[g,s]@M%P
                if g=="C":s=3-s
        return M,s
    results={}
    for s in (1,2):
        if not np.array_equal(word("CC",s)[0],J):
            raise ValueError("C2 not canonical parity")
        for name,w in (("C4","CCCC"),("D3","DDD"),("CD56","CD"*56),
                       ("C2_vs_CD28","CC"+"dc"*28),
                       ("R7","cdcdcddcdd"*7)):
            # Efficiently evaluate base word then power when it preserves phase.
            if name in ("CD56","R7"):
                base="CDCD" if name=="CD56" else "cdcdcddcdd"
                B,t=word(base,s)
                if t!=s:raise ValueError("relator base changes phase")
                count=14 if name=="CD56" else 7
                M=I.copy()
                while count:
                    if count&1:M=B@M%P
                    B=B@B%P;count//=2
                target=s
            else:
                M,target=word(w,s)
            results[f"{s}:{name}"]=bool(target==s and np.array_equal(M,I))
    if not all(results.values()):raise ValueError("source quotient relator failed")
    return {"status":"CANONICAL_MODEL_SIGNED_SECTION","model_only":True,
            "fixed_zeta_embedding":Z,"generators":{f"{g}:{s}":v for (g,s),v in records.items()},
            "quotient_relators_mod31":results}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--cover",type=Path)
    ap.add_argument("--atlas",action="store_true")
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args()
    if a.atlas:
        import check_toe_atlas_mirror as atlas
        C=atlas.inv(atlas.P)@atlas.C@atlas.P%3
        D=atlas.inv(atlas.P)@atlas.D@atlas.P%3
    elif a.cover:
        cover=json.loads(a.cover.read_text())
        C,D=parse_cover(cover)
        if any(any(cover["canonical_"+g]["affine_ell_F3"]) for g in ("C","D")):
            raise ValueError("nonzero affine source: parity normalization not justified")
    else:ap.error("provide actual cover or original ATLAS donor")
    result=replay(C,D)
    result["source_chart"]="original ATLAS donor" if a.atlas else "literal corrected MM quotient"
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,indent=2)+"\n")
    print(result["status"])

if __name__=="__main__":main()
