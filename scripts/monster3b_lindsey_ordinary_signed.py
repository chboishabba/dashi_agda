#!/usr/bin/env python3
"""Lindsey (1971), Trans. AMS 157, 189-204, DOI 10.1090/S0002-9947-1971-0283097-8.
Exact ordinary 6.Suz:2 via the complex Leech lattice; original author's
six generators, congruences and theorem reused. New DASHI quotient chart
and fixed-word transport. No Magma, GAP or mmgroup needed for this source.
"""
import argparse, hashlib, json
from pathlib import Path
from fractions import Fraction
import numpy as np
import sympy as S
from sympy.matrices.normalforms import hermite_normal_form
from monster3b_steel_ordinary12_to90 import (
    unpack, pack, transpose, inverse_matrix, symmetric_square, block,
    conjugate, product, tr, pair,
)
DOI="https://doi.org/10.1090/S0002-9947-1971-0283097-8"
CROWS="010000000000\n200000000000\n000100000000\n002000000000\n000001000000\n000020000000\n000000010000\n000000200000\n000000000010\n000000000001\n000000002000\n000000000200"
DROWS="001000000000\n112000000000\n202000000000\n000010000000\n121220000000\n000000100000\n000000001000\n000000000100\n000001000000\n000001121200\n011212110210\n011210201001"
HASHES=("ddd4919ab560f78b065aa08e309bd047942cdb7bb52a1474da84d54d35a031c2","433ba0f0373995b159859df00dd5a5005355fdbf8b59a31d651aeaf43ffcd15f")
CBASE=[2,7,3,-2,3,4,7,3,1,3,-2,3,6,4,-4,1,7,-4,5,3,-5,5,-4,-5,3,1,-5,1,1,3]
DBASE=[-1,-2,6,5,6,6,6,-1,3,-6,-4,6,-2,1,-5,-4,-4,-6,1,-3,1,-1,-2,-3,-3,7,7,-2,-2,-1]
CONJ=[-5,4,4,2,7,4,-4,2,2,-6,-5,-5,-1,-6,4,1,-5,-1,4,5,-5,4,-2,6,2,1,-4,-3,-3,-4]
CW=CBASE*45
DW=[-x for x in CONJ[::-1]]+DBASE*6+CONJ
TROWS=["222012011101","011221110021","101021021002","012000212000","022112112022","001021211011","111122110220","111221200201","110211101010","001222101020","112220100221","000221200021"]
SETS=[[1,2,3,4,5,6],[1,2,3,7,8,9],[1,2,4,9,10,11],[1,2,5,7,10,12],[1,3,4,8,10,12],[1,3,5,9,11,12],[1,4,5,7,8,11],[2,3,4,7,11,12],[2,3,5,8,10,11],[2,4,5,8,9,12],[3,4,5,7,9,10]]

def require(ok, why):
    if not ok: raise ValueError(why)
def rr(A):
    A=np.array(A,dtype=np.int64).copy()%3
    k=0; piv=[]
    for c in range(A.shape[1]):
        p=next((i for i in range(k,len(A)) if A[i,c]),None)
        if p is None: continue
        A[[k,p]]=A[[p,k]]; A[k]=A[k]*A[k,c]%3
        v=A[:,c].copy(); v[k]=0
        A=(A-np.outer(v,A[k]))%3
        k+=1; piv.append(c)
        if k==len(A): break
    return A,piv
def mod3(A): return np.array(A.tolist(),dtype=np.int64)%3
def pwr(A,k):
    R=np.eye(len(A),dtype=A.dtype)
    while k:
        if k&1:R=R@A
        A=A@A;k//=2
    return R
def eq(A,B): return np.array_equal(A,B)
def read(rows):return np.array([[int(c) for c in r] for r in rows],dtype=np.int64)

def lattice():
    I=S.eye(24); w=S.Matrix([[0,-1],[1,-1]])
    th=S.eye(2)+2*w; j=S.Matrix([[1,-1],[0,-1]])
    W=S.diag(*[w]*12); J=S.diag(*[j]*12); Theta=S.diag(*[th]*12)
    B=I
    def row(entries):
        r=S.zeros(1,24)
        for i,a,b in entries:r[0,2*i]=a;r[0,2*i+1]=b
        return r
    def cond(row,mod):
        nonlocal B
        for fac in ((1,3) if mod==9 else (1,)):
            require(all(x%fac==0 for x in row*B),"congruence stage")
            r=[int(x/fac) for x in row*B]
            if not any(x%3 for x in r):continue
            k=next(i for i,x in enumerate(r) if x%3)
            K=S.eye(24); K[k,k]=3
            for i in range(24):
                if i!=k:K[k,i]=(-r[i]*pow(r[k]%3,-1,3))%3
            B=hermite_normal_form(B*K)
    # Lindsey equations (3.1)-(3.4) on a+b*zeta coordinates.
    for i in range(1,12):cond(row([(0,1,1),(i,-1,-1)]),3)
    for ss in SETS:
        for s in (ss,sorted(set(range(1,13))-set(ss))):
            for a,b in ((1,0),(0,1)):cond(row([(i-1,a,b) for i in s]),3)
    cond(row([(i,1,1) for i in range(12)])+row([(0,3,3)]),9)
    require(B.det()==3**18,"Lindsey lattice index")
    U=S.BlockMatrix([[w**(i*k%3) for k in range(3)] for i in range(3)]).as_explicit()
    U=S.diag(*[th.inv()]*3)*U
    J3=S.diag(*[j]*3); Ub=J3*U*J3
    def perm(cycles):
        p=list(range(12))
        for cy in cycles:
            for i,k in zip(cy,cy[1:]+cy[:1]):p[i-1]=k-1
        M=S.zeros(24)
        for i,k in enumerate(p):M[2*k,2*i]=1;M[2*k+1,2*i+1]=1
        return M
    G=[S.diag(U,Ub,Ub,U),S.diag(*[w]*6,*[w**2]*6),
        perm([[1,2,3],[7,8,9],[10,11,12]]),
        perm([[4,5,6],[7,8,9],[10,12,11]]),
        perm([[1,2,6],[7,9,10],[8,12,11]]),
        perm([[1,2,8],[5,10,4],[6,11,12]]),J]
    Bi=B.inv(); mats=[Bi*g*B for g in G]
    require(all(all(x.q==1 for x in g) and g.det() in (-1,1) for g in mats),"lattice automorphism")
    gram=S.diag(*[S.Matrix([[2,-1],[-1,2]])]*12)
    require(all(g.T*gram*g==gram for g in G),"Hermitian real metric")
    Z=Bi*W*B
    require(all(x.q==1 for x in Z),"central lattice action")
    # Compute the quotient by theta L inside L/3L; do not reduce
    # rational entries directly at the ramified prime.
    V=mod3(Bi*Theta*B); piv=rr(V)[1]
    require(len(piv)==12,"theta image rank")
    K=V[:,piv]
    p=rr(np.column_stack([K,np.eye(24,dtype=np.int64)]))[1]
    require(len(p)==24,"quotient complement")
    X=np.column_stack([K,np.eye(24,dtype=np.int64)[:,[i-12 for i in p[12:]]]])
    Xi=mod3(S.Matrix(X.tolist()).inv_mod(3))
    q=[(Xi@mod3(g)@X%3)[12:,12:] for g in mats]
    require(all(not np.any((Xi@mod3(g)@X%3)[12:,:12]) for g in mats),"theta image invariant")
    return B,Bi,W,Z,mats,X,Xi,q

def run():
    B,Bi,W,Z,mats,X,Xi,q=lattice()
    # Replay fixed source words over characteristic zero, with Python
    # integers rather than int64 intermediates.
    ma=[np.array(g.tolist(),dtype=object) for g in mats]
    mi=[np.array(g.inv().tolist(),dtype=object) for g in mats]
    def ev(word):
        A=np.eye(24,dtype=object)
        for x in word:A=A@(ma[x-1] if x>0 else mi[-x-1])
        return A
    Z=np.array(Z.tolist(),dtype=object); I=np.eye(24,dtype=object)
    C,D0=ev(CW),ev(DW)
    for rows,want in zip((CROWS,DROWS),HASHES):
        require(hashlib.sha256(("1     3    12    12\n"+rows+"\n").encode()).hexdigest()==want,"ATLAS source hash")
    AC,AD=read(CROWS.splitlines()),read(DROWS.splitlines())
    t=read(TROWS)
    require(len(rr(t)[1])==12,"chart invertibility")
    def quo(M):
        return (Xi@np.array(M,dtype=np.int64)%3@X%3)[12:,12:]
    c,d=quo(C),quo(D0)
    require(eq(t@c%3,AC@t%3) and eq(t@d%3,AD@t%3),"same pinned quotient")
    require(eq(quo(Z),np.eye(12,dtype=np.int64)),"central phase killed by quotient")
    def zpow(A):
        return next((k for k in range(3) if eq(A,pwr(Z,k))),None)
    phase_rows=[]; selected=[]
    for k in range(3):
        D=pwr(Z,k)@D0
        Q=C@D@C@D@D
        ci,di=pwr(C,3),pwr(D,2)
        R=I.copy()
        for x in "cdcdcddcdd":R=R@(ci if x=="c" else di)
        r7,q7=zpow(pwr(R,7)),zpow(pwr(Q,7))
        phase_rows.append({"D_rephase":k,"Q7":q7,"R7":r7})
        if q7==0:selected.append((k,D,R))
    require(len(selected)==1,"unique standard D")
    k,D,R=selected[0]
    checks={"C4":eq(pwr(C,4),I),"C2_minus_I":eq(C@C,-I),
        "D3":eq(pwr(D,3),I),"CD56":eq(pwr(C@D,56),I),
        "C2_CD28":eq(C@C,pwr(C@D,28)),
        "Q7":eq(pwr(C@D@C@D@D,7),I),"R7_zeta":eq(pwr(R,7),Z),
        "C_inverts_zeta":eq(C@Z,pwr(Z,2)@C)}
    require(all(checks.values()),"ordinary source relators")
    # E = C D C^-1; signed C is semilinear in Eisenstein coordinates.
    E=C@D@pwr(C,3)
    def eisen(g,anti=False):
        A=B*S.Matrix(g.tolist())*Bi
        require(A*W==((-S.eye(24)-W)*A if anti else W*A),"signed field action")
        return [[[str(A[2*i,2*j]),str(A[2*i+1,2*j])] for j in range(12)] for i in range(12)]
    raw={"C":eisen(C,True),"D":eisen(D),"E":eisen(E)}
    def cj(A):return [[conjugate(x) for x in row] for row in A]
    def derived(A):
        H=symmetric_square(transpose(inverse_matrix(A)))
        return {"12":pack(A),"78":pack(H),"90":pack(block(A,H))}
    out={"schema":"monster3b-lindsey-ordinary-signed-v1","source":DOI,
        "field_polynomial":[1,1,1],"lattice_index":3**18,
        "atlas_sha256":list(HASHES),"quotient_T":t.tolist(),
        "C_word":CW,"D_word_before_standard_phase":DW,"standard_D_rephase":k,
        "central_phase_rows":phase_rows,"checks":checks,
        "matrix_convention":"left columns; C acts by A sigma",
        "ordinary_generators":raw,"signed_operators":{},
        "actual_Monster_Hom_intertwiner_verified":False,
        "literal_MM_D_phase_verified":False}
    for name in ("D","E"):
        A=unpack(raw[name]);out["signed_operators"][name]={"plus":derived(A),"minus":derived(cj(A))}
    A=unpack(raw["C"])
    # A sigma on K^12 splits into A from minus to plus and
    # conjugate(A) from plus to minus under the two embeddings.
    out["signed_operators"]["C"]={"plus_to_minus":derived(cj(A)),"minus_to_plus":derived(A)}
    out["D_standard_trace12"]=pair(tr(unpack(raw["D"])))
    return out

def attach_cover(out,receipt):
    """No fabricated literal MM word or source packet. Only attach after
    original cover receipt provides the additional signed Q^7 value."""
    if not receipt.get("actual_mmgroup_used"):raise ValueError("actual cover required")
    a=receipt.get("ATLAS_GF3_intertwiner",{})
    if a.get("intertwiner_dimension")!=1 or not a.get("form_transport_passed"):
        raise ValueError("original source chart not attached")
    for key in ("canonical_C_word","canonical_D_word","original_source_blob_sha"):
        if not receipt.get(key):raise ValueError("missing literal source identity "+key)
    rel=receipt["central_cover_relators"]
    if rel["ATLAS_R7"]["central_z_power"]!=1:raise ValueError("signed R7 mismatch")
    for key in ("C4","D3","CD56","C2_vs_CD28"):
        if rel[key]["central_z_power"]!=0:raise ValueError("literal relator mismatch "+key)
    q=rel.get("ATLAS_Q7",{}).get("central_z_power")
    if q not in (0,1,2):
        return {"status":"BLOCKED_LITERAL_MM_Q7","required_word":"CDCDD","known_R7":1}
    # For Q=CDCDD, twisting D by z^b shifts Q^7 by b.
    return {"status":"SOURCE_PHASE_ATTACHED_CONDITIONAL_ON_AUTHENTIC_RECEIPT",
        "C_word":receipt["canonical_C_word"],"D_word":receipt["canonical_D_word"],
        "D_relative_to_standard_phase":q,"R7":1,
        "actual_numeric_Hom_witness":False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out",type=Path,default=Path("build/monster3b-lindsey/ordinary_signed.json"))
    p.add_argument("--cover",type=Path)
    a=p.parse_args(); r=run()
    if a.cover:
        raw=a.cover.read_bytes(); r["cover_attachment"]=attach_cover(r,json.loads(raw))
        r["cover_sha256"]=hashlib.sha256(raw).hexdigest()
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(r,indent=2)+"\n")
    print(json.dumps({"out":str(a.out),"checks":r["checks"],"D_trace":r["D_standard_trace12"],"central_phase_rows":r["central_phase_rows"],"cover_attachment":r.get("cover_attachment")}))
if __name__=="__main__":main()
