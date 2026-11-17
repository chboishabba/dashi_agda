#!/usr/bin/env python3
"""D4-only 9+3 -> 12+Sym²(12)=90, with explicit rational D4 intertwiner.

Consumes existing D4 type/character geometry:
  DASHI/Biology/TernaryMonsterSymmetryCandidateExact.agda
  DASHI/Biology/D4NineCellOrbitCompressionExact.agda
  DASHI/Foundations/D4SO3NineIrrepRestrictionExact.agda
  DASHI/Moonshine/Monster3BNormalizerBridge.agda
  DASHI/Wikimedia/IbrahimMonster3BSuzukiQuotientDescentCorrectionExact.agda

WARNING: neither the 6.Suz faithful 78 nor the selected normalizer action
is identified here. Sym² of faithful complex 12 kills 6.Suz's central C2.
Full 6.Suz same-object matching requires separate class/quotient evidence.
"""
from itertools import product
import json,hashlib,argparse
from pathlib import Path
IR={"A1":(1,1),"A2":(1,-1),"B1":(-1,1),"B2":(-1,-1)}
TARGET={"A1":23,"A2":5,"B1":13,"B2":13,"E":18}
def comp(x,y):return [(x[j][0],s*x[j][1]) for j,s in y]
def pw(x,n):
    z=[(i,1) for i in range(len(x))]
    for _ in range(n):z=comp(x,z)
    return z
def tr(x):return sum(s for i,(j,s) in enumerate(x) if i==j)
def chr(r,s):return (tr(pw(r,0)),tr(pw(r,2)),tr(r),tr(s),tr(comp(r,s)))
def from_ir(c):
    r=[];s=[]
    for name,(a,b) in IR.items():
        for _ in range(c[name]):
            j=len(r);r.append((j,a));s.append((j,b))
    for _ in range(c["E"]):
        j=len(r);r.extend(((j+1,1),(j,-1)))
        s.extend(((j,1),(j+1,-1)))
    assert pw(r,4)==pw(r,0) and pw(s,2)==pw(s,0)
    assert comp(s,comp(r,s))==pw(r,3)
    return r,s
def sym2(g):
    n=len(g);pairs=[(i,j) for i in range(n) for j in range(i,n)]
    index={v:k for k,v in enumerate(pairs)}
    return [(index[tuple(sorted((g[i][0],g[j][0])))],g[i][1]*g[j][1]) for i,j in pairs]
def direct(x,y):return list(x)+[(len(x)+i,s) for i,s in y]
def sch(c):
    e,h,q,a,b=c
    return ((e*e+e)//2,(h*h+e)//2,(q*q+h)//2,(a*a+e)//2,(b*b+e)//2)
def irreps(ch):
    ir={"A1":(1,1,1,1,1),"A2":(1,1,1,-1,-1),
        "B1":(1,1,-1,1,-1),"B2":(1,1,-1,-1,1),"E":(2,-2,0,0,0)}
    v={k:sum(w*x*y for w,x,y in zip((1,1,2,2,2),ch,row)) for k,row in ir.items()}
    assert all(t>=0 and t%8==0 for t in v.values())
    return {k:t//8 for k,t in v.items()}
def apply(g,v):
    out=[0]*len(v)
    for i,(j,s) in enumerate(g):
        if v[i]:out[j]+=s*v[i]
    return out
def plus(v,w,t=1):return [x+t*y for x,y in zip(v,w)]
def canon(r,s,p=101):
    n=len(r);r2=pw(r,2);piv={};cols=[];names=[];counts={}
    def take(v):
        w=[x%p for x in v]
        for k,z in sorted(piv.items()):
            if w[k]:w=[(x-w[k]*y)%p for x,y in zip(w,z)]
        support=[k for k,x in enumerate(w) if x]
        if not support:return False
        k=support[0];iv=pow(w[k],-1,p)
        piv[k]=[x*iv%p for x in w];return True
    for name,lr,ls in (("A1",1,1),("A2",1,-1),("B1",-1,1),("B2",-1,-1)):
        count=0
        for i in range(n):
            v=[int(i==j) for j in range(n)]
            v=plus(v,apply(s,v),ls)
            v=plus(v,apply(r,v),lr)
            v=plus(v,apply(r2,v))
            if not any(v):continue
            assert apply(r,v)==[lr*x for x in v] and apply(s,v)==[ls*x for x in v]
            if take(v):cols.append(v);names.append(name);count+=1
        counts[name]=count
    pair=[]
    for i in range(n):
        v=[int(i==j) for j in range(n)]
        v=plus(v,apply(s,v))
        v=plus(v,apply(r2,v),-1)
        if not any(v):continue
        rv=apply(r,v)
        assert apply(s,v)==v and apply(s,rv)==[-x for x in rv]
        assert apply(r,rv)==[-x for x in v]
        if take(v):
            assert take(rv)
            pair.append((v,rv))
    for v,rv in pair:
        cols.extend((v,rv));names.extend(("E+","E-"))
    counts["E"]=len(pair)
    assert len(cols)==n and len(piv)==n
    return cols,names,counts
def nine_cell():
    # centre,N,E,S,W,NW,NE,SE,SW; source TernaryMonsterSymmetryCandidate
    rmap=(0,2,3,4,1,6,7,8,5)
    smap=(0,1,4,3,2,6,5,8,7)
    r=[(j,1) for j in rmap];s=[(j,1) for j in smap]
    assert chr(r,s)==(9,1,1,3,3)
    assert irreps(chr(r,s))=={"A1":3,"A2":0,"B1":1,"B2":1,"E":2}
    return r,s
def roots():
    out=[]
    for a in range(13):
      for b in range(13-a):
       for c in range(13-a-b):
        for d in range(13-a-b-c):
         e2=12-a-b-c-d
         if e2%2:continue
         e2//=2
         cts=dict(A1=a,A2=b,B1=c,B2=d,E=e2)
         if len(from_ir(cts)[0])!=12:continue
         x=chr(*from_ir(cts))
         if tuple(u+v for u,v in zip(x,sch(x)))==(90,18,2,18,18):
            out.append((cts,x))
    return out
def audit():
    possible=roots()
    assert len(possible)==3
    nine={"A1":3,"A2":0,"B1":1,"B2":1,"E":2}
    containing=[(c,ch) for c,ch in possible if all(c[k]>=v for k,v in nine.items())]
    assert len(containing)==1
    selected,selected_ch=containing[0]
    assert selected=={"A1":4,"A2":0,"B1":2,"B2":2,"E":2}
    r9,s9=nine_cell()
    # U12 = actual nine-position permutation module plus 3 signed lines
    r12=direct(r9,[(0,1),(1,-1),(2,-1)])
    s12=direct(s9,[(0,1),(1,1),(2,-1)])
    assert chr(r12,s12)==selected_ch
    r78,s78=sym2(r12),sym2(s12)
    assert len(r78)==78 and chr(r78,s78)==sch(selected_ch)
    r90,s90=direct(r12,r78),direct(s12,s78)
    oldr,olds=from_ir(TARGET)
    assert chr(r90,s90)==chr(oldr,olds)==(90,18,2,18,18)
    assert irreps(chr(r90,s90))==TARGET
    cb,cn,cc=canon(r90,s90)
    ob,on,oc=canon(oldr,olds)
    assert cn==on and cc==oc==TARGET
    # Explicit rational intertwiner on canonical bases:
    # T(ob[i])=cb[i] for every i. Both integer bases have full rank over F101,
    # hence over Q; each basis has the SAME signed D4 canonical block matrices.
    fields={}
    for p in (31,103,223):
        bc,_,ranks=canon(r90,s90,p)
        old,_,orr=canon(oldr,olds,p)
        assert ranks==orr==TARGET
        omega=next(t for t in range(2,p) if pow(t,3,p)==1)
        fields[str(p)]={"primitive_root_order3":omega,"rank_Cnew":90,"rank_Cold":90,
                        "char_2_invertible":True,"model_only_not_historical_Barraclough_matrices":True}
    # From the *source-backed* irreducible Sym²(12) of 3.Suz,
    # predict central scalar fingerprints without claiming the Monster
    # selected 78 family or Barraclough diagonal-quotient orientation.
    # Z[zeta] coordinates: a+b*zeta, zeta²=-1-zeta.
    zeta=[(1,0),(0,1),(-1,-1)]
    centre_rows=[]
    for phase12 in (1,2):
        for dual in (False,True):
            phase78=((-2 if dual else 2)*phase12)%3
            v12=zeta[phase12];v78=zeta[phase78]
            chi3=(12*v12[0]+78*v78[0],
                  12*v12[1]+78*v78[1])
            chi6=(-12*v12[0]+78*v78[0],
                  -12*v12[1]+78*v78[1])
            assert chi3[1]!=0  # Not a pure 90-point permutation trace
            centre_rows.append(dict(phase12=phase12,dual_sym2_78=dual,
                                    centre_C2_character=66,
                                    centre_C3_character=chi3,
                                    centre_C6_character=chi6))
    return dict(status="exact_D4_9plus3_symmetric_square_Q_intertwiner_passed",
       original_nine_cell_irreps=nine,
       three_12dimensional_D4_roots=[dict(multiplicities=c,character=ch) for c,ch in possible],
       unique_12_root_containing_nine_cell=selected,
       12_character=selected_ch,78_character=chr(r78,s78),
       90_character=chr(r90,s90),90_irreps=TARGET,
       explicit_intertwiner_over_Q="T = C_new * inverse(C_old); basis columns generated by canon()",
       old_basis_sha256=hashlib.sha256(json.dumps(ob).encode()).hexdigest(),
       new_basis_sha256=hashlib.sha256(json.dumps(cb).encode()).hexdigest(),
       rational_rank_certificate="both canonical integer matrices have rank90 mod101",
       source_finite_field_crosschecks=fields,
       source_irreducible_6Suz_Sym2_12_degree78=True,\n       source_sym2_78_descends_to_3Suz=True,\n       model_central_C2_C3_C6_fingerprints=centre_rows,\n       actual_Monster_selected_78_is_Sym2_12="unverified",
       full_monster_inertia_action_established=False,
       false_promotion_warning="Sym² of faithful 6.Suz degree12 kills its central involution; 6.Suz faithful degree78 cannot be that Sym²")
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--receipt",type=Path)
    a=p.parse_args();out=json.dumps(audit(),indent=2)+"\n"
    if a.receipt:a.receipt.write_text(out)
    print(out,end="")
