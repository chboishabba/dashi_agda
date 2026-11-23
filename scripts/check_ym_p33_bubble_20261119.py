#!/usr/bin/env python3
"""Exact configured P33 cubic bubble, two contraction orders.
Raw labelled Wilson derivatives; no effective-action symmetry factors.
"""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from functools import lru_cache
from check_ym_p33_configured_contractions_20261119 import N,O,neg,diff,weight,green
from check_ym_p33_fourier_vertices_20261119 import SITES,PLANES,phase,terms,slot_coords,add,mul,scale,ZERO

def plus(p,q):return tuple((a+b)%4 for a,b in zip(p,q))
@lru_cache(None)
def local_vertex(external,a,b):
    # Translate the external wave to the plaquette origin; retain both internal positions.
    out=defaultdict(lambda:ZERO)
    for mu,nu in PLANES:
        slots=slot_coords(O,mu,nu)
        for where,c in terms((external,(*a,O),(*b,O)),mu,nu):
            x,y,z=(slots[s][0] for s in where)
            out[y,z]=add(out[y,z],scale(phase(external[2],x),F(c,24)))
    return {k:v for k,v in out.items() if v!=ZERO}

def momentum_vertex(external,a,b,p,q):
    # Fourier transform of the full labelled vertex / volume.
    out=ZERO
    for (y,z),v in local_vertex(external,a,b).items():
        out=add(out,mul(v,mul(phase(p,y),phase(q,z))))
    return out

@lru_cache(None)
def coordinate_kernel(d1,d2,k):
    # Direct position-space product of Green kernels, external translation phase.
    out=ZERO
    for t in SITES:
        out=add(out,scale(phase(k,t),green(plus(t,d1))*green(plus(t,d2))))
    return out

def bubble_coordinate(left,right):
    if right[2]!=neg(left[2]):return ZERO
    out=ZERO
    for a,b in product(product(range(4),range(1,4)),repeat=2):
        for (y,z),v in local_vertex(left,a,b).items():
            for (u,w),h in local_vertex(right,a,b).items():
                out=add(out,mul(mul(v,h),coordinate_kernel(diff(y,u),diff(z,w),left[2])))
    return scale(out,N)

def bubble_momentum(left,right):
    if right[2]!=neg(left[2]):return ZERO
    out=ZERO
    for a,b in product(product(range(4),range(1,4)),repeat=2):
        if not local_vertex(left,a,b) or not local_vertex(right,a,b):continue
        for p in SITES:
            q=neg(plus(left[2],p))
            v=momentum_vertex(left,a,b,p,q)
            h=momentum_vertex(right,a,b,neg(p),neg(q))
            out=add(out,scale(mul(v,h),weight(p)*weight(q)))
    return out

def main():
    for axis,other,k in [(0,0,O),(1,1,(1,0,0,0)),(0,0,(1,0,0,0)),(0,1,(1,1,0,0))]:
        left=(axis,1,k);right=(other,1,neg(k))
        c=bubble_coordinate(left,right);m=bubble_momentum(left,right)
        assert c==m,(left,right,c,m)
        print('bubble',axis,other,k,c,flush=True)
    print('PASS four exact coordinate/Fourier cubic bubble comparisons, configured zero mode retained')
if __name__=='__main__':main()
