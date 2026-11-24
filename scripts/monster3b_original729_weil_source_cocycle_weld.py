#!/usr/bin/env python3
"""M3B-L10B/L12R: REUSE the repo's existing exact 729D Weil compiler.

No new 729-dimensional representation is constructed. Imports the
repo-owned scripts/toe_cyclotomic_operator.py from the older ATLAS/D4
source lane and applies its exact support/phase polynomial to the
ACTUAL full-mmgroup corrected C,D quotient matrices already in the
authenticated canonical-cover receipt.

Compute:
  * original 729 Schr vacuum K_g[0,0] / (zeta-zeta²)^rank, including ZERO
  * exact Q(zeta3) projective cocycle of model 729 action for D,E=CDC^-1,
    C², outer C swapping phase, and the true 10-letter R whose R^7=z3B
  * K_R^7, and the exact inverse-cocycle multiplicity-sector relator
    scalar required by the real Monster central character ζ_s.

This is a mathematical *chosen Weil gauge*, not proof that this choice
has already been identified with the 729 extension on W_s: true source
H_s <-> Monster W_s compatibility and standard 6.Suz words are separate.
For a zero vacuum entry, flag and refuse to divide: use a different
Schr point projector or column rather than silently making k0 nonzero.

Only NumPy and the existing repository 729 compiler are required.
No Magma, GAP, mmgroup execution, or native 196884D matrix is used.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import sys
import numpy as np

from toe_cyclotomic_operator import compile_shape
from monster3b_atlas_mmgroup_cross_source_intertwiner_gate import inverse as f3_inverse

Q0=(F(0),F(0))
Q1=(F(1),F(0))
ZETA=(F(0),F(1))
DELTA=(F(1),F(2))   # ζ-ζ² = 1+2ζ; Δ²=-3
ROOTS=(Q1,ZETA,(F(-1),F(-1)))
I12=np.eye(12,dtype=np.int64)

def add(a,b):return (a[0]+b[0],a[1]+b[1])
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],
                       a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def inv(a):
    n=a[0]*a[0]-a[0]*a[1]+a[1]*a[1]
    if n==0: raise ZeroDivisionError("zero cyclotomic model scalar")
    return ((a[0]-a[1])/n,-a[1]/n)
def power(a,k):
    if k<0:return power(inv(a),-k)
    z=Q1
    while k:
        if k&1:z=mul(z,a)
        a=mul(a,a);k//=2
    return z
def pack(a):return [str(a[0]),str(a[1])]
def rootsix(a):
    for sign in (1,-1):
        for k in range(3):
            root=tuple(sign*x for x in ROOTS[k])
            if a==root:return f"{'-' if sign==-1 else ''}zeta^{k}"
    return None

def key(v):return sum(int(x)*3**(len(v)-j-1) for j,x in enumerate(v))
def trits(i,n=6):
    out=[0]*n
    for j in range(n-1,-1,-1):out[j]=i%3;i//=3
    if i:raise ValueError("Schr index beyond 3^6")
    return out

def column(R,j):
    """Exact nonzero original K(row,j) for canonical scalar=1.

    Reuses the EXISTING compiler's support matrix, origin and quadratic
    phase, rather than re-deriving 729 Heisenberg action in a new owner.
    """
    n=len(R["origin"]);rank=R["rank"]
    x=trits(j,n)
    B=np.asarray(R["B"],dtype=np.int64).reshape(n,rank)
    a=np.asarray(R["a"],dtype=np.int64)
    origin=np.asarray(R["origin"],dtype=np.int64)
    lin=R["linear"];sq=R["square"];cross=R["cross"]
    out={}
    for ts in product(range(3),repeat=rank):
        y=(origin+a@x+B@np.asarray(ts,dtype=np.int64))%3
        u=x+list(ts)
        q=R["constant"]+sum(p*t for p,t in zip(lin,u))
        q+=sum(p*t*t for p,t in zip(sq,u))
        k=0
        for v in range(len(u)):
            for w in range(v+1,len(u)):
                q+=cross[k]*u[v]*u[w];k+=1
        idx=key(y)
        if idx in out:raise AssertionError("repo compiler nonindependent vacuum support")
        out[idx]=ROOTS[q%3]
    if len(out)!=3**rank:raise AssertionError("repo Weil support cardinality incorrect")
    return out

def _rank3(matrix):
    A=np.asarray(matrix,dtype=np.int64).copy()%3
    nrows,ncols=A.shape;k=0
    for col in range(ncols):
        p=next((j for j in range(k,nrows) if A[j,col]),None)
        if p is None:continue
        A[[k,p]]=A[[p,k]]
        A[k]=A[k]*int(A[k,col])%3
        for j in range(nrows):
            if j!=k and A[j,col]:
                A[j]=(A[j]-int(A[j,col])*A[k])%3
        k+=1
        if k==nrows:break
    return k

def _inverse3(matrix):
    A=np.asarray(matrix,dtype=np.int64)%3
    n=len(A)
    if A.shape!=(n,n):raise ValueError("GF3 inverse matrix not square")
    M=np.concatenate((A,np.eye(n,dtype=np.int64)),axis=1)
    for col in range(n):
        pivot=next((i for i in range(col,n) if M[i,col]),None)
        if pivot is None:raise ValueError("chosen Weil B-support rows not independent")
        M[[col,pivot]]=M[[pivot,col]]
        M[col]=M[col]*int(M[col,col])%3
        for i in range(n):
            if i!=col and M[i,col]:
                M[i]=(M[i]-int(M[i,col])*M[col])%3
    return M[:,n:]

def kernel_entry(R,row,j):
    """One exact original compiled Weil coefficient, O(r²), no 729 loop.

    Source 729 compiler supplies B,origin,a and phase polynomial. The
    support equation origin+a*x+B*t=y has UNIQUE t because B is full
    rank. Solve it once per entry with a cached left inverse of B.
    """
    n=len(R["origin"]);rk=R["rank"]
    x=np.asarray(trits(j,n),dtype=np.int64)
    y=np.asarray(trits(row,n),dtype=np.int64)
    a=np.asarray(R["a"],dtype=np.int64)
    v=(y-np.asarray(R["origin"],dtype=np.int64)-a@x)%3
    B=np.asarray(R["B"],dtype=np.int64).reshape(n,rk)
    if rk:
        if "_support_pivots" not in R:
            chosen=[]
            for k in range(n):
                if _rank3(B[chosen+[k]])>len(chosen):
                    chosen.append(k)
                if len(chosen)==rk:break
            if len(chosen)!=rk:
                raise AssertionError("original repo Weil support B lacks rank")
            R["_support_pivots"]=chosen
            R["_support_inverse"]=_inverse3(B[chosen]).tolist()
        inds=R["_support_pivots"]
        inverse=np.asarray(R["_support_inverse"],dtype=np.int64)
        t=(inverse@v[inds])%3
        if not np.array_equal((B@t)%3,v):return Q0
        ts=t.tolist()
    else:
        if np.any(v):return Q0
        ts=[]
    u=x.tolist()+ts
    q=R["constant"]+sum(a*b for a,b in zip(R["linear"],u))
    q+=sum(a*b*b for a,b in zip(R["square"],u))
    idx=0
    for i in range(len(u)):
        for j in range(i+1,len(u)):
            q+=R["cross"][idx]*u[i]*u[j];idx+=1
    return ROOTS[q%3]

def f3_mul(A,B):return (A@B)%3
def f3_pow(A,k):
    z=I12.copy()
    while k:
        if k&1:z=f3_mul(z,A)
        A=f3_mul(A,A);k//=2
    return z
def check_sympl(A,lam):
    C=np.zeros((12,12),dtype=np.int64)
    C[6:,:6]=np.eye(6,dtype=np.int64)
    J=(C.T-C)%3
    if not np.array_equal((A.T@J@A)%3,lam*J%3):
        raise ValueError("genuine 12D source does not preserve symplectic form up to centre λ")

def model(A,lam,s):
    check_sympl(A,lam)
    R=compile_shape(A,lam,s)
    R["source_phase"]=s
    R["target_phase"]=s*lam%3
    return R

def coeff_of_product(g,h,gh):
    """With h acting first, evaluate (K_g K_h) at a nonzero K_gh pivot."""
    target=column(gh,0)
    row=next(iter(target))
    h0=column(h,0)
    value=Q0
    for j,c_h in h0.items():
        kg=kernel_entry(g,row,j)
        if kg!=Q0:value=add(value,mul(kg,c_h))
    return mul(value,inv(target[row]))

def cocycle(A,lamA,B,lamB,source_phase):
    """K_A on phase λ_B*s follows K_B on phase s."""
    AA,BB=f3_mul(A,B),lamA*lamB%3
    ra=model(A,lamA,source_phase*lamB%3)
    rb=model(B,lamB,source_phase)
    rab=model(AA,BB,source_phase)
    raw=coeff_of_product(ra,rb,rab)
    rg,rh,rgh=ra["rank"],rb["rank"],rab["rank"]
    # Deterministic unitary gauge: Δ^-r K_g; no scalar left floating.
    # Over Q(ζ3), |Δ|²=3. This is a model convention and may have a
    # nontrivial μ6 multiplier on composition.
    unit=mul(raw,power(DELTA,rgh-rg-rh))
    return {"input_phase":source_phase,"intermediate_phase":source_phase*lamB%3,
        "output_phase":source_phase*lamA*lamB%3,
        "ranks":[rg,rh,rgh],
        "unscaled_729_multiplier_Qzeta3":pack(raw),
        "unitary_gauge_multiplier_Qzeta3":pack(unit),
        "unitary_gauge_root_of_unity":rootsix(unit),
        "unitary_gauge_mu6":rootsix(unit) is not None}

def k00(A,lam,s):
    kernel=model(A,lam,s)
    z=column(kernel,0).get(0)
    if z is None:return {"support_contains_zero":False,
         "k0_nonzero":False,"rank":kernel["rank"],
         "source_phase":s,"target_phase":s*lam%3}
    value=mul(z,power(DELTA,-kernel["rank"]))
    return {"support_contains_zero":True,"k0_nonzero":True,
       "k0_unitary_model_Qzeta3":pack(value),
       "k0_vacuum_normalized_ratio_Qzeta3":pack(Q1),
       "unnormalized_vacuum_phase_Qzeta3":pack(z),
       "rank":kernel["rank"],
       "source_phase":s,"target_phase":s*lam%3}

def parse_cover(cover):
    if cover.get("schema")!="monster3b-full-MM-Heisenberg-canonical-lifts-v1":
        raise ValueError("requires ORIGINAL source-canonical corrected C/D group receipt")
    if cover.get("actual_mmgroup_used") is not True:
        raise ValueError("source receipt did not use genuine Monster MM")
    if (cover.get("canonical_C",{}).get("central_multiplier_mod3"),
        cover.get("canonical_D",{}).get("central_multiplier_mod3"))!=(2,1):
        raise ValueError("original centre signed λ(C),λ(D) mismatch")
    C=np.asarray(cover["canonical_C"]["matrix_F3"],dtype=np.int64)%3
    D=np.asarray(cover["canonical_D"]["matrix_F3"],dtype=np.int64)%3
    if C.shape!=(12,12) or D.shape!=(12,12):
        raise ValueError("original 12D affine corrected GF3 quotient shape")
    if not np.array_equal(f3_pow(C,4),I12) or not np.array_equal(f3_pow(D,3),I12):
        raise ValueError("original corrected Monster C4/D3 quotient mismatch")
    return C,D

def word_matrix(word,C,D):
    ci=np.asarray(f3_inverse(C.tolist()),dtype=np.int64)
    di=np.asarray(f3_inverse(D.tolist()),dtype=np.int64)
    out=I12.copy()
    for w in word:
        if w not in "CDcd":raise ValueError("invalid original source word")
        m={"C":C,"D":D,"c":ci,"d":di}[w]
        out=f3_mul(out,m)
    return out

def source_calculation(cover):
    C,D=parse_cover(cover)
    ci=np.asarray(f3_inverse(C.tolist()),dtype=np.int64)
    E=f3_mul(f3_mul(C,D),ci)
    R=word_matrix("cdcdcddcdd",C,D)
    if not np.array_equal(f3_pow(R,7),I12):
        raise ValueError("source ATLAS quotient ten-letter R does NOT have order7")
    if not np.array_equal(f3_pow(E,3),I12):
        raise ValueError("source inner E=CDC^-1 not order3")
    rel=cover.get("central_cover_relators",{})
    if rel.get("ATLAS_R7",{}).get("central_z_power") not in (1,2):
        raise ValueError("missing source-original full Monster R7=z nontrivial centre")
    zr=rel["ATLAS_R7"]["central_z_power"]
    result={"schema":"monster3b-reused-toe-original729-weil-cochain-v1",
      "original_Monster_canonical_source_blob_sha":cover.get("original_source_blob_sha"),
      "literal_full_Monster_ATLAS_R7_z_power":zr,
      "actual_same_object_729_to_Wzeta_gauge_identified":False,
      "original_6Suz_standard_word_attached":False,
      "chosen_scalar_gauge":"Delta^-rank; Delta=ζ-ζ²=1+2ζ; unitary Schr model only",
      "same_Monster_group_words":"D, E=CDC^-1, C, R=cdcdcddcdd",
      "phases":{}}
    for phase in (1,2):
        named={"D":(D,1),"E":(E,1),"C":(C,2),"C2":(f3_pow(C,2),1),
             "DE":(f3_mul(D,E),1),"ED":(f3_mul(E,D),1),
             "R":(R,1)}
        vacuum={k:k00(A,lam,phase) for k,(A,lam) in named.items()}
        pair={}
        for label,left,right in (
            ("D_E","D","E"),("E_D","E","D"),("C_C","C","C"),
            ("D_D","D","D"),("E_E","E","E")):
            a,la=named[left];bb,lb=named[right]
            pair[label]=cocycle(a,la,bb,lb,phase)
        # Power R^7 in the exact finite model. This uses 6 successive
        # original repo-compiled K_R*K_R^j cocycles, no 729x729 matrix.
        Rpow=R.copy()
        product_scalar=Q1
        staircase=[]
        for j in range(1,7):
            item=cocycle(R,1,Rpow,1,phase)
            scalar=item["unitary_gauge_multiplier_Qzeta3"]
            ratio=(F(scalar[0]),F(scalar[1]))
            product_scalar=mul(product_scalar,ratio)
            staircase.append({"power":j+1,**item})
            Rpow=f3_mul(R,Rpow)
        if not np.array_equal(Rpow,I12):
            raise ValueError("R seven-power multiplication failed original quotient")
        central_expected=power(ZETA,phase*zr)
        # Genuine W_R^7=ζ^(phase*zr) in the ORIGINAL Monster
        # Wζ sector; the 90D multiplicity relator must compensate the
        # exact Schr model seven-power in the selected unitary gauge.
        multiplicity_relator=mul(central_expected,inv(product_scalar))
        result["phases"][str(phase)]={
           "vacuum":vacuum,"pairs":pair,
           "R7_model_729_unitary_scalar_Qzeta3":pack(product_scalar),
           "R7_model_729_mu6":rootsix(product_scalar),
           "R7_original_full_Monster_central_scalar_Qzeta3":pack(central_expected),
           "R7_FORCED_90D_multiplicity_scalar_in_this_Weil_gauge_Qzeta3":
             pack(multiplicity_relator),
           "R7_90D_gauge_is_model_relative_not_same_object":True,
           "R7_sequential_729_cocycle":staircase}
    return result

def selftest():
    assert mul(DELTA,DELTA)==(F(-3),F(0))
    assert power(DELTA,-2)==(F(-1,3),F(0))
    I=I12.copy()
    assert k00(I,1,1)["k0_unitary_model_Qzeta3"]==["1","0"]
    assert cocycle(I,1,I,1,1)["unitary_gauge_multiplier_Qzeta3"]==["1","0"]
    for j in (0,1,7,728):
        row1=column(model(I,1,1),j)
        assert row1=={j:Q1}
        assert kernel_entry(model(I,1,1),j,j)==Q1
    # A genuine rank-6 symplectic Fourier transform, not a generic
    # 90-dimensional synthetic model. F^2=-I and F^4=I.
    f=np.zeros((12,12),dtype=np.int64)
    f[:6,6:]=np.eye(6,dtype=np.int64)
    f[6:,:6]=2*np.eye(6,dtype=np.int64)
    assert np.array_equal(f3_pow(f,2),2*I%3)
    rank=k00(f,1,1)["rank"]
    assert rank==6
    cf=cocycle(f,1,f,1,1)
    assert cf["unitary_gauge_mu6"]
    return {"status":"PASS_PURE_EXISTING_729_MODEL",
       "Delta_squared":"-3","unitary_rank6_Fourier":True,
       "identity_729_cocycle":"1",
       "Fourier_square_model_multiplier":cf["unitary_gauge_root_of_unity"],
       "original_MM_source_executed_here":False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cover",type=Path)
    p.add_argument("--out",type=Path,default=Path(
        ".dashi/monster3b-mmgroup/original729_weil_90_cocycle.json"))
    p.add_argument("--selftest",action="store_true")
    a=p.parse_args()
    if a.selftest:res=selftest()
    else:
        if a.cover is None:p.error("original mmgroup canonical cover receipt required")
        res=source_calculation(json.loads(a.cover.read_text()))
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(res,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":res.get("status","MODEL_SOURCE_COCHAIN_EXACT"),
       "out":str(a.out),
       "source_729_compiler":"toe_cyclotomic_operator.py",
       "actual_Monster_729_identified":res.get(
          "actual_same_object_729_to_Wzeta_gauge_identified",False)},indent=2))
if __name__=="__main__":main()
