"""Signed capacity commuting square, in doubled integer Fourier coordinates.

Restriction commutes with grouping; zero mode retained. All bounds concern
original row weight on odd-parity carriers, not auxiliary assignment counts.
"""
from check_pnp_affine_normal_components import bits, canon, chart, satisfies
from check_pnp_normal_boundary_join import value


def add(M,a,c):
    v=M.get(a,0)+c
    if v:M[a]=v
    else:M.pop(a,None)


def row_ledger(r,u,V):
    M={}
    for j in bits(r):
        add(M,0,1)
        add(M,value(V,1<<j),1 if u>>j&1 else -1)
    return M


def pull(M,t,T):
    """2*w(t XOR Ty): coalesce collisions with their actual signs."""
    Q={}
    for a,c in M.items():
        add(Q,value(T,a),-c if (a&t).bit_count()%2 else c)
    return Q


def bounds(M):
    """Independent signed envelope intersected with odd integer weights."""
    C=M.get(0,0);S=sum(abs(c) for a,c in M.items() if a)
    l=(C-S+1)//2;h=(C+S)//2
    return l+(l%2==0),h-(h%2==0)


def evaluate(M,z):
    return sum(-c if (a&z).bit_count()%2 else c for a,c in M.items())


def screen(n,R,H,caps,B):
    """Return (retained carrier, witness, reason). None carrier is exact empty.
    Every strict step forces original-coordinate normals; at most n rounds.
    A stalled nonempty carrier is UNKNOWN, never a negative answer.
    Caller handles budget refusal transactionally.
    """
    B.pay('signed_square_scope',1+(n+1)*(1+len(H)+len(R)))
    assert H==canon(H) and canon(H+tuple((r,1) for r in R))==H
    assert len(R)==len(caps)
    while True:
        d=n-len(H)
        B.pay('signed_square_chart',1+(n+1)**2*(1+len(H)))
        u,V=chart(n,H)
        B.pay('signed_square_origin',1+n+sum(r.bit_count() for r in R))
        if all((r&u).bit_count()<=c for r,c in zip(R,caps)):
            assert satisfies(u,H,())
            return H,u,'origin'
        B.pay('signed_square_group',1+sum(r.bit_count() for r in R)*(1+d))
        M=[row_ledger(r,u,V) for r in R]
        if any(bounds(m)[0]>c for m,c in zip(M,caps)):
            return None,None,'floor'
        free=tuple(j for j in range(n) if j not in {a.bit_length()-1 for a,b in H})
        pins=[]
        for m,c in zip(M,caps):
            if bounds(m)[1]<=c:continue
            for a in sorted(m):
                if not a:continue
                B.pay('signed_square_orientations',2*(1+d)*(1+d+len(m)))
                bad=[]
                for b in (0,1):
                    t,T=chart(d,((a,b),))
                    if bounds(pull(m,t,T))[0]>c:bad.append(b)
                if len(bad)==2:return None,None,'both_orientations'
                if bad:
                    p=sum(1<<free[j] for j in bits(a))
                    pins.append((p,bad[0]^1))
        B.pay('signed_square_pin_join',1+(n+1)*(1+len(H)+len(pins))**2)
        K=canon(H+tuple(pins))
        if K is None:return None,None,'pin_conflict'
        if K==H:return H,None,'stalled'
        assert len(K)>len(H)
        H=K
