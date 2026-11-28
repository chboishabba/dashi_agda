"""Finite model controls: sparse incidence and local placed-window checks.
The templates below are a toy identity tableau, not an arbitrary candidate.
"""
from check_pnp_cook_quadratic_seek import QuadraticCookSeek
from collections import Counter
from itertools import combinations

def sparse():
    out=[]
    for p in (2,3,5,7,11):
        # Lines of the affine plane F_p^2. Every point belongs to p+1 lines.
        D=[frozenset(x*p+(m*x+b)%p for x in range(p)) for m in range(p) for b in range(p)]
        D += [frozenset(x*p+y for y in range(p)) for x in range(p)]
        assert all(len(a&b)<=1 for a,b in combinations(D,2))
        load=Counter(i for d in D for i in d);C=max(load.values())
        assert C==p+1 and len(D)==p*C and len(D)<=p*p*C
        out.append((p,p*p,len(D),C,len(D)//C))
    return out

def windows(T):
    # Identity recurrence on the three cells in each 2x3 window.
    F=tuple(c for i in range(1,4) for c in (((i,False),(i+3,True)),((i,True),(i+3,False))))+(((0,True),),)
    Q=QuadraticCookSeek(T,1,1,F,(((0,False),(1,True)),),(1,),(1,1,1))
    x=[1]*(Q.G+Q.C)
    def check(t,j,z):
        return all(any(z[Q.trans_coord(i,t,j)]==b for i,b in c) for c in F)
    assert all(check(t,j,x) for t in range(T) for j in range(Q.J))
    # Formula seek of first placed clause token is independent of the assignment.
    k=3*(Q.transition_prefix(0)+Q.window_prefix(0,0))
    assert tuple(Q.bit(k+i) for i in range(3))==(1,1,0)
    for i in range(Q.R,Q.S):
        y=x.copy();y[i]^=1
        assert not all(check(t,j,y) for t in range(T) for j in range(Q.J))
    y=x.copy();y[Q.S-1]^=1
    assert check(0,0,y) and not check(T-1,Q.J-1,y)
    assert tuple(Q.bit(k+i) for i in range(3))==(1,1,0)
    return T,Q.S-Q.R,T*Q.J

def main():
    print(dict(sparse=sparse(),window_controls=[windows(T) for T in (2,3,5,8,12)]))
if __name__=='__main__':main()
