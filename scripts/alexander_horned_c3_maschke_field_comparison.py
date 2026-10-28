#!/usr/bin/env python3
"""Field-controlled C3 Maschke test on the SAME cyclotomic companion matrix.

Original mathematics: Maschke's theorem; the cyclotomic polynomial
Phi_3(X)=X^2+X+1; C3 rotation about the diagonal in Q^3.
DASHI provenance: C3CyclotomicRealDescentExact,
C3FourierConjugationExact, R3HodgeCrossExact,
AlexanderHornedC3AmbientRotationExact,
AlexanderHornedC3MaschkeR3Exact.

This tests the finite matrices exactly, including field changes.
It proves no physical spectral zero, 3B Monster correspondence,
Dirac operator Fredholm index or actual wild exterior geometry.
"""
from itertools import product
from fractions import Fraction

A=((0,-1),(1,-1))
I2=((1,0),(0,1))
J3=((1,1,1),)*3
R3=((0,0,1),(1,0,0),(0,1,0))

def matmul(A,B,p):
    return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(len(B)))%p
                       for j in range(len(B[0]))) for i in range(len(A)))

def add(A,B,p):
    return tuple(tuple((a+b)%p for a,b in zip(row1,row2))
                 for row1,row2 in zip(A,B))

def scale(k,A,p):
    return tuple(tuple(k*a%p for a in row) for row in A)

def zero(n):
    return tuple((0,)*n for _ in range(n))

def eye(n):
    return tuple(tuple(int(i==j) for j in range(n)) for i in range(n))

def matvec(A,v,p):
    return tuple(sum(a*b for a,b in zip(row,v))%p for row in A)

def rank(A,p):
    M=[list(a) for a in A];row=0
    for col in range(len(M[0])):
        pivot=next((k for k in range(row,len(M)) if M[k][col]%p),None)
        if pivot is None:continue
        M[row],M[pivot]=M[pivot],M[row]
        inverse=pow(M[row][col],-1,p)
        M[row]=[inverse*x%p for x in M[row]]
        for k in range(len(M)):
            if k==row:continue
            factor=M[k][col]%p
            M[k]=[(a-factor*b)%p for a,b in zip(M[k],M[row])]
        row+=1
    return row

def det2(M,p):
    return (M[0][0]*M[1][1]-M[0][1]*M[1][0])%p

def evaluate(p):
    M=scale(1,A,p)
    assert matmul(matmul(M,M,p),M,p)==I2
    assert add(add(matmul(M,M,p),M,p),I2,p)==zero(2)
    roots=[x for x in range(p) if (x*x+x+1)%p==0]
    fixed=[v for v in product(range(p),repeat=2)
           if matvec(M,v,p)==v]
    sign_visible=(-1)%p!=1
    if p==3:
        # The same cyclotomic 2-plane becomes a nonsplit self-extension
        # 0 -> trivial -> M -> trivial -> 0; N=A-I !=0, N^2=0.
        N=add(M,scale(-1,I2,p),p)
        assert N!=zero(2) and matmul(N,N,p)==zero(2)
        assert rank(N,p)==1 and len(fixed)==p
        assert roots==[1]
        # In char 3, the trivial diagonal axis lies *inside*
        # the sum-zero plane, so the former direct decomposition
        # fails to split, a stronger invariant than '3 is not invertible'.
        axis=(1,1,1)
        assert matvec(R3,axis,p)==axis and sum(axis)%p==0
        assert matmul(J3,J3,p)==zero(3) and J3!=zero(3)
    else:
        assert len(fixed)==1
        inv3=pow(3,-1,p)
        P=scale(inv3,J3,p)
        assert matmul(P,P,p)==P
        assert matmul(P,R3,p)==P and matmul(R3,P,p)==P
        assert rank(P,p)==1
        assert rank(add(eye(3),scale(-1,P,p),p),p)==2
        assert all(matvec(P,(x,y,z),p)==(inv3*(x+y+z)%p,)*3
                   for x,y,z in product(range(p),repeat=3))
        assert (len(roots)==0 or len(roots)==2)
        if p==5:assert roots==[]
        if p==7:
            assert roots==[2,4]
            P2=scale(pow((2-4)%p,-1,p),
                     add(M,scale(-4,I2,p),p),p)
            P4=scale(pow((4-2)%p,-1,p),
                     add(M,scale(-2,I2,p),p),p)
            assert matmul(P2,P2,p)==P2 and matmul(P4,P4,p)==P4
            assert matmul(P2,P4,p)==zero(2)
            assert add(P2,P4,p)==I2
            assert rank(P2,p)==rank(P4,p)==1
            assert matmul(M,P2,p)==scale(2,P2,p)
            assert matmul(M,P4,p)==scale(4,P4,p)
        if p==2:assert roots==[] and not sign_visible
    return {'characteristic':p,'Maschke':p!=3,'roots':roots,
            'cyclotomic_fixed_dimension':1 if p==3 else 0,
            'spin_sign_distinguishable':sign_visible}

def rational_check():
    q=Fraction(1,3)
    coords=[(Fraction(a,2),Fraction(b,3),Fraction(c,5))
            for a,b,c in product(range(-3,4),repeat=3)]
    for x,y,z in coords:
        m=q*(x+y+z)
        v=(m,m,m)
        rem=(x-m,y-m,z-m)
        assert tuple(v[i]+rem[i] for i in range(3))==(x,y,z)
        assert sum(rem)==0
        assert q*(z+x+y)==m
        a=x;b=-z
        if x+y+z==0:
            assert (a,b-a,-b)==(x,y,z)
    # Transverse chart (a,b-a,-b) has the prescribed companion action.
    for a,b in product((Fraction(i,7) for i in range(-8,9)),repeat=2):
        x=(a,b-a,-b)
        assert (x[2],x[0],x[1])==(-b,a,b-a)
    print("PASS: exact rational 1+2 Reynolds splitting and same C3 transverse companion")

def main():
    rational_check()
    for p in (2,3,5,7,11):
        r=evaluate(p)
        print("p={characteristic}: Maschke={Maschke}, roots={roots}, "
              "FixCyclotomic={cyclotomic_fixed_dimension}, "
              "spin(-1) visible={spin_sign_distinguishable}".format(**r))
    print("PASS: SAME C3 matrices semisimple F2/F5/F7/F11 and nonsplit F3")
    print("PASS: F3 nilpotent (A-I)^2=0 and J^2=0 vs F5/F7 Reynolds projectors")
    print("NOT TESTED: Agda kernel, 2I->E8 McKay functor, wild E Dirac zero mode")

if __name__=="__main__":main()
