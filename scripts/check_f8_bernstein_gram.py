"""F8 signed Gram specialization of existing Bernstein restriction consumer.
AB orthogonal mass; retain source Bernstein controls, uniform source bound.
"""
import sys,json,math
from fractions import Fraction as Q
from functools import lru_cache
import numpy as np
from check_f8_kernel_hermite_residual import I,D,U,rat,axis,stack
import check_f8_bernstein_branch as branch

@lru_cache(None)
def transform(n):
    # coefficient in shifted Legendre basis, exact rational beta moments
    return tuple(tuple((2*j+1)*sum(((-1)**(j-l)*math.comb(j,l)*math.comb(j+l,l)*Q(math.factorial(n)*math.factorial(i+l),math.factorial(i)*math.factorial(n+l+1)) for l in range(j+1)),Q(0)) for i in range(n+1)) for j in range(n+1))

def apply(p,i):
    a=axis(p,i);rows=[]
    for row in transform(len(a.l)-1):
        q=I(0)
        for j,c in enumerate(row):
            if c:q=q+rat(c)*a[j]
        rows.append(q)
    b=stack(rows);return I(np.moveaxis(b.l,0,i),np.moveaxis(b.h,0,i))

oldstats=branch.stats

def stats(p,den):
    peak,jensen=oldstats(p,den);a=apply(apply(p,0),1);q=np.zeros(a.l.shape[2:])
    for i in range(a.l.shape[0]):
        for j in range(a.l.shape[1]):
            m=a[i,j].mag();q=U(q+U(U(m*m)/((2*i+1)*(2*j+1))))
    # den is positive lower bound of actual denominator on physical branch.
    energy=U(np.max(q,axis=0)/D(np.asarray(den)**2))
    return peak,np.minimum(jensen,energy)

def exact():
    import sympy as S
    x=S.symbols('x');count=0
    for n in (2,3,5):
        T=S.Matrix(transform(n));W=S.diag(*(S.Rational(1,2*j+1) for j in range(n+1)))
        G=S.Matrix(n+1,n+1,lambda i,j:S.Rational(math.comb(n,i)*math.comb(n,j),(2*n+1)*math.comb(2*n,i+j)))
        assert T.T*W*T==G;count+=1
        assert T.det()!=0;count+=1
        for i in range(n+1):
            assert S.expand(sum(T[j,i]*S.legendre(j,2*x-1) for j in range(n+1))-S.binomial(n,i)*x**i*(1-x)**(n-i))==0;count+=1
    # signed cancellation and unequal axes, source controls remain independent
    a=np.arange(4*6*3,dtype=float).reshape(4,6,3)%7-3;p=I(a);v=apply(apply(p,0),1)
    assert v.l.shape==a.shape
    for l in range(3):
        t=S.Matrix(transform(3))*S.Matrix(a[:,:,l].astype(int))*S.Matrix(transform(5)).T
        for i in range(4):
            for j in range(6):assert Q(float(v.l[i,j,l]))<=Q(t[i,j])<=Q(float(v.h[i,j,l]))
        count+=1
    a=I(np.array([1.,-1.]).reshape(2,1,1));_,j=oldstats(a,1.);_,g=stats(a,1.);assert g>=1/3 and g<.334 and j>=1;count+=1
    return count

def run(n,mode,j,h,depth):
    checks=exact();branch.stats=stats
    try:out=branch.run(n,mode,j,h,depth)
    finally:branch.stats=oldstats
    out.update(gram_checks=checks,scope='signed AB Gram and source Jensen; whole selected source slab, all targets; no receiver rerun')
    return out
if __name__=='__main__':print(json.dumps(run(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),2.**-int(sys.argv[4]),int(sys.argv[5]))),flush=True)
