"""Bounded exact-variable-separator character join for the actual F3/CNF sector.

No F2 normal-space labels are identified with F3 coordinates. Each shared
Boolean coordinate is conditioned once; its observable contribution occurs
once. All boundary orientations are enumerated only under an explicit width
cap. Interior refusal contributes an absolute spectral envelope, not zero.
"""
from itertools import product
from math import isqrt
from fractions import Fraction as Q
from check_pnp_signed_component_histogram import component_bounds,convolve,rref

def separator(F,cols,target,R,width):
    R=tuple(sorted(R));n=len(R)
    rr=rref(tuple(tuple(cols[v][i] for v in R)+(t,) for i,t in enumerate(target)),n)
    if rr is None:return None
    rows,_=rr
    if () in F:return None
    factors=[(0,c,frozenset(abs(l)-1 for l in c)) for c in F]
    factors += [(1,row,frozenset(v for v,a in zip(R,row[:-1]) if a)) for row in rows]
    best=None
    for cut in sorted({n//3,n//2,2*n//3}):
        if not 0<cut<n:continue
        left=set(R[:cut]); sides=[[],[]]; supports=[set(),set()]
        for kind,f,S in factors:
            j=int(2*len(S&left)<len(S))
            sides[j].append((kind,f));supports[j].update(S)
        shared=supports[0]&supports[1]
        a=supports[0]-shared;b=supports[1]-shared
        if not a or not b or len(shared)>width:continue
        a.update(set(R)-supports[0]-supports[1])
        key=(len(shared),-min(len(a),len(b)),cut)
        if best is None or key<best[0]:best=(key,tuple(sorted(shared)),(tuple(sorted(a)),tuple(sorted(b))),sides)
    return best

def boundary_contrast(F,cols,target,offset,R,w,local_width=6,boundary_width=3):
    """Return (lo,hi,receipt) or None on separator refusal.
    Receipt contains exact retained head and absolute omitted energies.
    """
    R=tuple(sorted(R));split=separator(F,cols,target,R,boundary_width)
    if split is None:return None
    _,S,parts,sides=split;pos={v:i for i,v in enumerate(R)}
    head=[Q(0)]*3;EL=ER=pair_radius=omitted=retained=0
    for bits in product(range(2),repeat=len(S)):
        pins=dict(zip(S,bits))
        shift=(offset+sum(cols[v][-1]*pins[v] for v in S))%3
        receipts=[]
        for I,fs in zip(parts,sides):
            G=[];rows=[];rhs=[]
            for kind,f in fs:
                if kind==0:
                    if any(abs(l)-1 in pins and pins[abs(l)-1]==int(l>0) for l in f):continue
                    G.append(tuple(l for l in f if abs(l)-1 not in pins))
                else:
                    rows.append(f)
                    rhs.append((f[-1]-sum(f[pos[v]]*pins[v] for v in S))%3)
            # Preserve global literal indices. Columns outside I are unused.
            C=tuple(tuple(row[pos[v]] if v in pos else 0 for row in rows)+(col[-1],)
                    for v,col in enumerate(cols))
            receipts.append(component_bounds(tuple(G),C,tuple(rhs),0,I,local_width,spectral=True))
        (a,c,h,e),(b,d,j,f)=receipts
        if not c or not d or not e or not f:
            retained+=1;continue
        if a and b:
            H=convolve(h,j)
            for k in range(3):head[k]+=w*(3*H[(k-shift)%3]-c*d)
            retained+=1
        else:
            EL+=e;ER+=f;pair_radius+=isqrt(4*e*f);omitted+=1
    # Integral unweighted contrast: floor sqrt is safe. Cauchy-Schwarz
    # needs ABSOLUTE energies, not a relative fraction of full mass.
    radius=abs(w)*min(pair_radius,isqrt(4*EL*ER))
    return tuple(x-radius for x in head),tuple(x+radius for x in head),dict(
        boundary=S,retained=retained,omitted=omitted,left_energy=EL,right_energy=ER,
        radius=radius,head=tuple(head))
