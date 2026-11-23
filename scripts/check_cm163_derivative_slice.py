#!/usr/bin/env python3
"""CM163 correction from diagonal and one fixed specialization of Phi_41.
Requires classical modularity, q expansion and Ramanujan identities.
No precomputed modular polynomial, numerical recognition or Masser theorem.
"""
from time import perf_counter
from sympy import Poly, symbols, ZZ, QQ, Rational, invert
from check_cm163_modular_diagonal import j_unit, convolution, diagonal


def slice_poly(p, K, logder_fn=None):
    n = p+1
    M = p*n
    J = j_unit(M)
    H = J[:]
    H[1] -= K
    if logder_fn is None:
        L = [0]*(M+1)
        for k in range(1,M+1):
            L[k] = k*H[k]-sum(H[i]*L[k-i] for i in range(1,k))
    else:
        L=logder_fn(H)
    N = [1]
    for k in range(1,n+1):
        v = sum(L[p*i]*N[k-i] for i in range(1,k+1))
        a,b=divmod(v,k)
        assert b==0
        N.append(a)
    # p odd: product of p zeta factors = 1; p+1 negative signs cancel.
    g = [0]*(n+1)
    g[0]=1
    g[p]=J[1]-K
    rem=convolution(g,N,n)
    powers=[[1]+[0]*n]
    for k in range(n):powers.append(convolution(powers[-1],J[:n+1],n))
    coeff=[0]*(n+1)
    for d in range(n,-1,-1):
        c=rem[n-d]; coeff[d]=c
        for k in range(d+1):rem[n-d+k]-=c*powers[d][k]
    assert not any(rem) and coeff[-1]==1
    return Poly.from_list(coeff[::-1],symbols('X'),domain=ZZ)


def main(diagonal_fn=diagonal, slice_fn=slice_poly):
    start=perf_counter()
    p=41; K=-640320**3
    P=diagonal_fn(p).shift(K)
    print('diagonal seconds',perf_counter()-start,flush=True)
    S=slice_fn(p,K).shift(K)
    print('slice seconds cumulative',perf_counter()-start,flush=True)
    assert P.nth(0)==P.nth(1)==S.nth(0)==S.nth(1)==0
    c20=S.nth(2); c30=S.nth(3)
    c11=P.nth(2)-2*c20
    c21=P.nth(3)/2-c30
    assert c20!=0
    x=symbols('alpha')
    m=Poly(41*x*x+81*x+41,x,domain=QQ)
    def red(v): return Poly(v,x,domain=QQ).rem(m)
    assert red(c20*(1+x*x)+c11*x).is_zero
    # y=alpha*x_local+beta*x_local^2; cubic equation determines beta.
    den=red((c11+2*c20*x)*(x*x-x))
    num=red(-2*(c30*(1+x**3)+c21*(x+x*x)))
    kappa=(num*invert(den,m)).rem(m)
    assert kappa.degree()==0
    kappa=kappa.nth(0)
    s2=4+3*Rational(K,K-1728)-6*K*kappa
    print('kappa',kappa)
    print('s2',s2)
    assert s2==Rational(77265280,90856689)
    assert (1-s2)/6==Rational(13591409,545140134)
    print('PASS exact CM correction, wall_seconds',perf_counter()-start)

if __name__=='__main__':main()
