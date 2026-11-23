#!/usr/bin/env python3
"""Original-ATLAS GF3 basis weld and strict Monster-side provenance boundary.

A local canonical symplectic chart of the *same* ATLAS representation is
not an independently sourced Monster E/Z(E) action. No Monster promotion.
Source owners: original ATLAS/AtlasRep; #1098 original vendoring; #1250.
"""
import hashlib
import json
from itertools import product
from pathlib import Path
from monster3b_atlas_source_word_order_d4_gate import parse_meataxe, mm, ident, neg, rank
from monster3b_atlas_actual_d4_word_witness import FORM_ROWS, SOURCE_DIGESTS

N=12
def tr(a): return [list(r) for r in zip(*a)]
def mv(a,v): return [sum(x*y for x,y in zip(row,v))%3 for row in a]
def pairing(v,j,w):return sum(x*y for x,y in zip(v,mv(j,w)))%3
def columns(v):return [list(r) for r in zip(*v)]
def inv(a):
    x=[r[:]+i[:] for r,i in zip(a,ident())]
    for k in range(N):
        z=next((i for i in range(k,N) if x[i][k]),None)
        if z is None:raise ValueError("rank deficient change of basis")
        x[k],x[z]=x[z],x[k]
        v=x[k][k];x[k]=[t*v%3 for t in x[k]]
        for i in range(N):
            if i!=k and x[i][k]:
                v=x[i][k]
                x[i]=[(t-v*u)%3 for t,u in zip(x[i],x[k])]
    return [r[N:] for r in x]
def symplectic_chart(j):
    remaining=[[int(k==i) for k in range(N)] for i in range(N)]
    E=[];F=[]
    while remaining:
        a=remaining[0]
        b=next((v for v in remaining if pairing(a,j,v)),None)
        if b is None:raise ValueError("degenerate form")
        b=[t*pairing(a,j,b)%3 for t in b]
        E.append(a);F.append(b);new=[]
        for v in remaining:
            w=[(x-pairing(v,j,b)*y+pairing(v,j,a)*z)%3 for x,y,z in zip(v,a,b)]
            if any(w) and rank(columns(new+[w]))>len(new):new.append(w)
        remaining=new
    return columns(E+F)
def nullspace(generator_pairs):
    # 144 unknown entries of X, equations XA_i=B_i X.
    system=[]
    for a,b in generator_pairs:
        for i in range(N):
            for j in range(N):
                row=[0]*(N*N)
                for k in range(N):row[i*N+k]=(row[i*N+k]+a[k][j])%3
                for k in range(N):row[k*N+j]=(row[k*N+j]-b[i][k])%3
                system.append(row)
    pivots=[];step=0
    for col in range(N*N):
        ix=next((i for i in range(step,len(system)) if system[i][col]),None)
        if ix is None:continue
        system[step],system[ix]=system[ix],system[step]
        scale=system[step][col]
        system[step]=[v*scale%3 for v in system[step]]
        for i in range(len(system)):
            if i!=step and system[i][col]:
                v=system[i][col]
                system[i]=[(x-v*y)%3 for x,y in zip(system[i],system[step])]
        pivots.append(col);step+=1
    basis=[]
    for free in range(N*N):
        if free in pivots:continue
        v=[0]*(N*N);v[free]=1
        for i,p in enumerate(pivots):v[p]=(-system[i][free])%3
        basis.append([v[k*N:(k+1)*N] for k in range(N)])
    return basis

def audit(root):
    base=root/"data"/"atlas"
    for path,expected in SOURCE_DIGESTS.items():
        if hashlib.sha256((base/path).read_bytes()).hexdigest()!=expected:
            raise ValueError("ATLAS original SHA256 mismatch "+path)
    C,D=[parse_meataxe(base/k) for k in SOURCE_DIGESTS]
    J=[[int(v) for v in s] for s in FORM_ROWS.splitlines()]
    assert rank(J)==12 and tr(J)==neg(J)
    assert mm(mm(tr(C),J),C)==neg(J)
    assert mm(mm(tr(D),J),D)==J
    T=symplectic_chart(J);Ti=inv(T)
    J0=mm(mm(tr(T),J),T)
    expected=[[0]*N for _ in range(N)]
    for k in range(6):expected[k][k+6]=1;expected[k+6][k]=2
    assert J0==expected and mm(T,Ti)==ident()
    canonical=[mm(mm(Ti,M),T) for M in (C,D)]
    for original,b in zip((C,D),canonical):assert mm(original,T)==mm(T,b)
    assert mm(mm(tr(canonical[0]),J0),canonical[0])==neg(J0)
    assert mm(mm(tr(canonical[1]),J0),canonical[1])==J0
    # Original C acts on Heisenberg centre by -1; D acts by +1.
    # J0=C0^T-C0 is the alternating part of the standard cocycle.
    cocycle=[[0]*N for _ in range(N)]
    for k in range(6):cocycle[k+6][k]=2
    assert [[(cocycle[i][j]-cocycle[j][i])%3 for j in range(N)]
            for i in range(N)]==J0
    defect_ranks=[]
    for g,lmb in zip(canonical,(2,1)):
        transported=mm(mm(tr(g),cocycle),g)
        defect=[[(transported[i][j]-lmb*cocycle[i][j])%3
                 for j in range(N)] for i in range(N)]
        assert defect==tr(defect)
        # q(x)=2 x^T defect x; polarization is defect since 4=1 mod3.
        for x,y in product(([0]*N,[1]+[0]*11,[0,1]+[0]*10),repeat=2):
            def q(v):return 2*pairing(v,defect,v)%3
            xy=[(a+b)%3 for a,b in zip(x,y)]
            assert (q(xy)-q(x)-q(y))%3==sum(a*b for a,b in zip(x,mv(defect,y)))%3
        defect_ranks.append(rank(defect))
    basis=nullspace(list(zip((C,D),canonical)))
    assert len(basis)==1 and rank(T)==12
    assert all(mm(m,T)==mm(T,b) for m,b in zip((C,D),canonical))
    # Independent negative controls: wrong generator identification is not an intertwiner.
    assert len(nullspace([(C,canonical[1]),(D,canonical[0])]))==0
    assert len(nullspace([(C,ident()),(D,ident())]))==0
    return dict(schema="monster3b-original-atlas-symplectic-basis-weld-v1",
                original_matrix_sha256_matched=True,
                same_source_basis_T=T, canonical_C=canonical[0],canonical_D=canonical[1],
                canonical_J=J0, source_form_rank=12,
                conjugating_T_invertible=True, generator_pair_transport=True,
                common_intertwiner_dimension=len(basis),
                cocycle_defect_ranks=defect_ranks,
                central_multiplier_C=2,central_multiplier_D=1,
                swapped_generator_negative_control=True,
                wrong_target_negative_control=True,
                independent_Monster_generator_pair_supplied=False,
                external_Monster_E_over_Z_intertwiner_certified=False,
                W_zeta_H_zeta_cocycle_promoted=False)
if __name__=="__main__":
    print(json.dumps(audit(Path(__file__).resolve().parents[1]),sort_keys=True,indent=2))
