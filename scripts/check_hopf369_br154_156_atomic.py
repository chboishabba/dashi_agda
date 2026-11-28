#!/usr/bin/env python3
"""Atomic/369 source cut: signed shell characters, KK lane BIDI, full 2p^2 Coulomb.
Finite selected operators; not an atomic-spectrum or quantum-gravity derivation.
"""
import argparse
from itertools import combinations, product
from collections import Counter
import sympy as s
from sympy.physics.wigner import gaunt
Q=s.Rational

def shell(n):
    return [(l,m,spin) for l in range(n) for m in range(-l,l+1) for spin in (-1,1)]

def chars():
    # orbital-only C3; separate order-three rephasing of spinorial rotation.
    # Rotation by 2pi/3 on spin alone has order six, not three.
    for n in range(1,10):
        S=shell(n); assert len(S)==2*n*n
        a=Counter(m%3 for l,m,spin in S)
        b=Counter((m+2*spin)%3 for l,m,spin in S)
        assert a[1]==a[2] and b[1]==b[2]
        tr=2 if n%3 else 0
        assert a[0]-a[1]==tr and b[0]-b[1]==-tr//2
    S=shell(2);assert Counter(m%3 for l,m,spin in S)=={0:4,1:2,2:2}
    assert Counter((m+2*spin)%3 for l,m,spin in S)=={0:2,1:3,2:3}
    assert Counter(m%3 for l,m,spin in shell(3))=={0:6,1:6,2:6}
    blocks=(((1,0),),((2,0),(2,1)),((3,0),(3,1)),((4,0),(3,2),(4,1)),((5,0),(4,2),(5,1)),((6,0),(4,3),(5,2),(6,1)),((7,0),(5,3),(6,2),(7,1)))
    assert [sum(2*(2*l+1) for n,l in b) for b in blocks]==[2,8,8,18,18,32,32]
    # In a filled subshell the determinant phase is neutral, even though
    # the one-particle character and the particle count are not the same.
    for n in range(1,10):
        assert sum(m for l,m,spin in shell(n))%3==0
        assert sum(m+2*spin for l,m,spin in shell(n))%3==0
    print('PASS BR154 actual atomic shell and spin-lift character, period partition and filled-shell determinant')

def lane():
    S=shell(2);P=[(x,y) for x,y in product((-1,0,1),repeat=2) if (x,y)!=(0,0)]
    # Marked site antipode paired with spin flip, not physical parity.
    reps=[p for p in P if p>tuple(-x for x in p)]
    spatial=[(l,m) for l,m,spin in S if spin==1]
    chart={(l,m,sg):tuple(sg*x for x in p) for (l,m),p in zip(spatial,reps) for sg in (-1,1)}
    assert len(set(chart.values()))==8
    assert all(chart[l,m,-sg]==tuple(-x for x in chart[l,m,sg]) for l,m,sg in S)
    K=s.Matrix([[0,0,1],[1,0,0],[0,1,0]]);I=s.eye(8)
    # Physical real p-rotation represented on each spin sector by an
    # order-three permutation of a Cartesian p basis (axis (1,1,1)).
    B=s.diag(1,1,K,K);assert B**3==I and B.trace()==2
    J=s.diag(I,B,B**2);F=s.kronecker_product(K,I);G=s.kronecker_product(K,B)
    assert J*F*J.T==G and J.T*J==s.eye(24) and G.trace()==0
    # Atomic s/p energies plus selected finite KK circle kinetic energy.
    es,ep,c=s.symbols('es ep c',real=True);h=s.diag(es,es,*([ep]*6));C=2*s.eye(3)-K-K.T
    H=s.kronecker_product(s.eye(3),h)+c*s.kronecker_product(C,I)
    Hp=J*H*J.T
    assert H*F==F*H and Hp*G==G*Hp
    assert Hp==s.kronecker_product(s.eye(3),h)+c*(2*s.eye(24)-G-G.T)
    assert s.kronecker_product(s.eye(3),B).trace()==6
    W=s.kronecker_product(s.ones(3,1)/s.sqrt(3),I);Wp=J*W
    assert Wp.T*Wp==I and (Hp*Wp-Wp*h).applyfunc(s.simplify)==s.zeros(24,8) and G*Wp==Wp
    print('PASS BR155 marked 3x8 chart, diagonal lane/atomic rotation BIDI and selected-mode energy intertwiner')

def coulomb():
    # Same Z=1 hydrogenic 2p radial source as atomic_369_p2_coulomb_exact.py.
    # Donor's F0,F2 exact rational values, no new radial approximation.
    F={0:Q(93,512),2:Q(45,512)}
    from functools import lru_cache
    @lru_cache(None)
    def angular(a,k,q,c,conj):
        return (-s.S.One)**(a+(q if conj else 0))*gaunt(1,k,1,-a,-q if conj else q,c)
    @lru_cache(None)
    def eri(a,b,c,d):
        return s.simplify(sum(4*s.pi*F[k]*angular(a,k,q,c,True)*angular(b,k,q,d,False)/(2*k+1) for k in (0,2) for q in range(-k,k+1)))
    modes=list(product((-1,0,1),(-1,1)));pairs=list(combinations(range(6),2))
    def direct(a,b,c,d):
        ma,sa=modes[a];mb,sb=modes[b];mc,sc=modes[c];md,sd=modes[d]
        return eri(ma,mb,mc,md) if sa==sc and sb==sd else 0
    V=s.Matrix(15,15,lambda i,j:direct(*pairs[i],*pairs[j])-direct(*pairs[i],*pairs[j][::-1]))
    assert V==V.T
    eig=V.eigenvals();assert eig=={Q(21,128):9,Q(237,1280):5,Q(111,512):1},eig
    for spin in (-1,1):
        ids=[k for k,(i,j) in enumerate(pairs) if modes[i][1]==modes[j][1]==spin]
        assert V[ids,ids]==Q(21,128)*s.eye(3)
    def wedge(A):
        return s.Matrix(15,15,lambda i,j:A[pairs[i][0],pairs[j][0]]*A[pairs[i][1],pairs[j][1]]-A[pairs[i][0],pairs[j][1]]*A[pairs[i][1],pairs[j][0]])
    # Magnetic spatial rotation remains diagonal and charge-conserving.
    for i,(a,b) in enumerate(pairs):
        for j,(c,d) in enumerate(pairs):
            if (modes[a][0]+modes[b][0]-modes[c][0]-modes[d][0])%3:assert V[i,j]==0
    # The cyclic m-label shift is a different action; full interacting
    # sector no longer has the accidental common-spin scalar symmetry.
    K=s.zeros(6)
    for i,(m,spin) in enumerate(modes):K[modes.index(((-1,0,1)[(m+2)%3],spin)),i]=1
    assert K**3==s.eye(6);W=wedge(K);assert W**3==s.eye(15)
    comm=V*W-W*V;assert comm!=s.zeros(15)
    print('BR156 projected Coulomb eigenvalues:',eig,'cyclic charge commutator rank:',comm.rank())
    print('PASS BR156 full 2p^2 antisymmetric spin-orbital Coulomb, physical rotation retained, bare charge shift obstructed')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['chars','lane','coulomb'],required=True)
    {'chars':chars,'lane':lane,'coulomb':coulomb}[p.parse_args().part]()
