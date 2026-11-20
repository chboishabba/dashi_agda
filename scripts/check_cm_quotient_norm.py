"""Small exact quotient norm oracle; no field assumptions on residue rings."""
import argparse
from random import Random
from sympy import Matrix, Poly, resultant, symbols, ZZ
from sympy.polys.matrices import DomainMatrix

t,q=symbols("t q")

def quotient_norm(h,p,n,r):
    if p<2 or n<0 or r<2 or not h or h[0]!=1:
        raise ValueError("requires p>=2, n>=0, r>=2, H(0)=1")
    h=h[:p*n+1]
    a=[sum(h[i]*q**(i//p) for i in range(j,len(h),p)) for j in range(p)]
    m=Matrix(p,p,lambda i,j:a[(i-j)%p]*(q if i<j else 1))
    d=Poly(DomainMatrix.from_Matrix(m).det().as_expr(),q,domain=ZZ)
    assert d.nth(0)==1
    return [int(d.nth(i))%r for i in range(n+1)]

def resultant_norm(h,p,n,r):
    # Reduce first in the monic quotient. Degree of second argument < p
    # avoids a degree-swapping sign ambiguity in the SymPy reference.
    h=h[:p*n+1]
    a=sum(c*q**(i//p)*t**(i%p) for i,c in enumerate(h))
    d=Poly(resultant(t**p-q,a,t),q,domain=ZZ)
    assert d.nth(0)==1
    return [int(d.nth(i))%r for i in range(n+1)]

def log_norm(h,p,n,r):
    # Independent scalar recurrence, not the packed production path.
    h=(h+[0]*(p*n+1))[:p*n+1]
    l=[0]
    for k in range(1,p*n+1):
        l.append((k*h[k]-sum(h[i]*l[k-i] for i in range(1,k+1)))%r)
    a=[1]
    for k in range(1,n+1):
        a.append(sum(l[p*i]*a[k-i] for i in range(1,k+1))*pow(k,-1,r)%r)
    return a

def main():
    rng=Random(9);count=0;logs=0
    for p in (2,3,5,7):
        for n in (1,2,3):
            for r in (4,9,25,121):
                h=[1]+[rng.randrange(-8,9) for _ in range(p*n)]
                a=quotient_norm(h,p,n,r)
                assert a==resultant_norm(h,p,n,r)
                count+=1
                from math import gcd
                if gcd(r,6 if n==3 else 2 if n==2 else 1)==1:
                    assert a==log_norm(h,p,n,r)
                    logs+=1
    print(f"PASS determinant/resultant {count}; logarithmic recurrence {logs}")

if __name__=="__main__":
    main()
