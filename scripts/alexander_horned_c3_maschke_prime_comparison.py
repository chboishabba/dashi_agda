#!/usr/bin/env python3
"""Exact same-matrix C3 comparison: nonmodular Maschke vs modular Jordan.

Owners: R3HodgeCrossExact, C3CyclotomicRealDescentExact,
C3FourierConjugationExact, NormalizedFibreAveragingExact,
IbrahimMonster3BWholeCharacterIsotypicBypassExact (mathlib Maschke).
Proof boundary: finite field arithmetic, NOT a Dirac eigenmode.
"""
from fractions import Fraction as F
from itertools import product

A=((0,-1),(1,-1))
R=((0,0,1),(1,0,0),(0,1,0)) # Existing horn rotateXYZ
def ident(n):return tuple(tuple(int(i==j) for j in range(n)) for i in range(n))
def zmat(n):return tuple(tuple(0 for _ in range(n)) for _ in range(n))
def mm(X,Y,p=None):
    return tuple(tuple((sum(X[i][k]*Y[k][j] for k in range(len(Y)))%p if p
             else sum(X[i][k]*Y[k][j] for k in range(len(Y))))
             for j in range(len(Y[0]))) for i in range(len(X)))
def add(X,Y,p=None):
    return tuple(tuple((x+y)%p if p else x+y for x,y in zip(u,v))
                 for u,v in zip(X,Y))
def scale(k,X,p=None):
    return tuple(tuple(k*x%p if p else k*x for x in row) for row in X)
def mpow(X,n,p=None):
    z=ident(len(X))
    for _ in range(n):z=mm(z,X,p)
    return z
def rank(X,p):
    a=[[x%p for x in row] for row in X];m,n=len(a),len(a[0]);r=0
    for j in range(n):
        i=next((i for i in range(r,m) if a[i][j]%p),None)
        if i is None:continue
        a[i],a[r]=a[r],a[i]
        u=pow(a[r][j],-1,p)
        a[r]=[x*u%p for x in a[r]]
        for k in range(m):
            if k!=r:
                d=a[k][j]
                a[k]=[(x-d*y)%p for x,y in zip(a[k],a[r])]
        r+=1
        if r==m:break
    return r
def apply(X,x,p):return tuple(sum(a*b for a,b in zip(row,x))%p for row in X)

def main():
    I3=ident(3);I2=ident(2)
    assert mpow(R,3)==I3
    P=scale(F(1,3),add(add(I3,R),mpow(R,2)))
    Q=add(I3,scale(-1,P))
    assert mpow(P,2)==P and mpow(Q,2)==Q
    assert mm(P,Q)==mm(Q,P)==zmat(3) and add(P,Q)==I3
    assert mm(R,P)==P and mm(R,Q)==mm(Q,R)
    assert P==tuple(tuple(F(1,3) for _ in range(3)) for _ in range(3))
    print("Q: same horn R3 C3 cycle gives actual Reynolds line + plane splitting")
    for p in (2,3,5,7):
        a=tuple(tuple(x%p for x in row) for row in A)
        assert mpow(a,3,p)==I2
        assert add(add(mpow(a,2,p),a,p),I2,p)==zmat(2)
        fixed={v for v in product(range(p),repeat=2) if apply(a,v,p)==v}
        roots=[x for x in range(p) if (x*x+x+1)%p==0]
        assert len(fixed)==(p if p==3 else 1)
        assert roots=={2:[],3:[1],5:[],7:[2,4]}[p]
        signLift=scale(-1,a,p)
        assert mpow(signLift,3,p)==scale(-1,I2,p)
        assert mpow(signLift,6,p)==I2
        if p!=3:
            pp=scale(pow(3,-1,p),add(add(I3,R,p),mpow(R,2,p),p),p)
            qq=add(I3,scale(-1,pp,p),p)
            assert mpow(pp,2,p)==pp and mpow(qq,2,p)==qq
            assert mm(pp,qq,p)==mm(qq,pp,p)==zmat(3)
            assert rank(pp,p)==1 and rank(qq,p)==2
            assert mm(R,pp,p)==pp
        if p==3:
            N=add(a,scale(-1,I2,p),p)
            assert N!=zmat(2) and mpow(N,2,p)==zmat(2)
            # All four lines of F3^2: the one fixed line has NO
            # stable complement, so this module is not semisimple.
            lines={frozenset(tuple(t*x%p for x in v) for t in range(p))
                   for v in product(range(p),repeat=2) if v!=(0,0)}
            stable=[L for L in lines if all(apply(a,v,p) in L for v in L)]
            assert len(lines)==4 and len(stable)==1
            assert next(iter(stable))==frozenset(fixed)
            S=add(add(I3,R,p),mpow(R,2,p),p)
            assert S!=zmat(3) and mpow(S,2,p)==zmat(3)
            assert rank(S,p)==1
            print("F3: N=A-I nonzero, N²=0, fixed line without invariant complement")
        elif p==5:
            assert len(roots)==0
            print("F5: Maschke applies, cyclotomic spin plane irreducible; +/- spin sign survives")
        elif p==7:
            E2=scale(pow((2-4)%p,-1,p),add(a,scale(-4,I2,p),p),p)
            E4=scale(pow((4-2)%p,-1,p),add(a,scale(-2,I2,p),p),p)
            assert add(E2,E4,p)==I2
            assert mpow(E2,2,p)==E2 and mpow(E4,2,p)==E4
            assert mm(E2,E4,p)==zmat(2)
            assert mm(a,E2,p)==scale(2,E2,p) and mm(a,E4,p)==scale(4,E4,p)
            print("F7: Maschke applies; two rank-one cyclotomic spectral idempotents")
        else:
            assert (p-1)%p==1
            print("F2: Maschke applies, but central +/- spin sign collapses")
        # Genuine 3-site free orbit x 2-spin action on six dimensions:
        T=tuple(tuple(R[i//2][j//2]*a[i%2][j%2]%p
                      for j in range(6)) for i in range(6))
        assert mpow(T,3,p)==ident(6)
        fixedRank=6-rank(add(T,scale(-1,ident(6),p),p),p)
        assert fixedRank==2 # ALSO true in characteristic 3!
        if p!=3:
            pr=scale(pow(3,-1,p),add(add(ident(6),T,p),mpow(T,2,p),p),p)
            assert mpow(pr,2,p)==pr and rank(pr,p)==2
        print(f"F{p}: free 3-site x 2-spin invariant dimension 2; "
              +("Maschke projector exists" if p!=3 else "averaging not defined"))
    print("PASS: same-action semisimple vs nonsemisimple, no physical mode inference")
if __name__=="__main__":main()
