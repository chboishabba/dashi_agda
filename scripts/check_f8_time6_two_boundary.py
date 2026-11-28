"""Original F8 high-time graph boundary ledger.

At the inner GN wall H_n=-6 Pi; at the outer collar R=W+V=0,
so H_t+N H_n=0. Differentiating the outgoing condition gives a lower-
order lapse commutator. The resulting high-time boundary quadratic form
is dissipative modulo explicit lower-order traces, not sign-free.

Exact algebraic interface, not an original-solution energy enclosure.
"""
from math import comb
import sympy as s


def outgoing_commutator(m, Njets, Hn):
    if len(Njets)<=m or len(Hn)<m:
        raise ValueError('insufficient lapse or lower normal jets')
    return -sum(comb(m,j)*Njets[j]*Hn[m-j] for j in range(1,m+1))


def exact():
    t,n=s.symbols('t n',positive=True)
    a=s.sinh(s.asinh(t)-n)
    N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    B=N*a**3
    h=s.Function('h')(t,n)
    outer=s.Rational(1,2)
    for m in range(7):
        v=s.diff(h,t,m)
        C=outgoing_commutator(m,[s.diff(N,t,j) for j in range(m+1)],
                              [s.diff(h,n,t,j) for j in range(m)])
        outgoing=s.diff(s.diff(h,t)+N*s.diff(h,n),t,m)
        assert s.expand(outgoing-s.diff(v,t)-N*s.diff(v,n)+C)==0
        q=s.symbols(f'q{m}',real=True)
        g=s.symbols(f'g{m}',real=True)
        nn=s.symbols(f'N{m}',positive=True)
        bb=s.symbols(f'B{m}',positive=True)
        flux=bb*(g-nn*q)*q
        completion=-bb*nn*(q-g/(2*nn))**2+bb*g*g/(4*nn)
        assert s.factor(flux-completion)==0
        assert s.simplify(completion.subs(g,0)+bb*nn*q*q)==0
        assert s.simplify(N.subs(n,outer))!=0
    z=s.Function('z')(t)
    pi=s.Function('pi')(t)
    g6=-6*s.diff(pi,t,6)
    inner=-t**3*s.diff(z,t)*g6
    correction=t**3*z*g6
    assert s.simplify(inner+s.diff(correction,t)-z*s.diff(t**3*g6,t))==0
    assert s.simplify(s.diff(t**3*g6,t)+6*(3*t*t*s.diff(pi,t,6)+t**3*s.diff(pi,t,7)))==0
    em,eps,wt,src=s.symbols('em eps wt src',positive=True)
    assert s.simplify(eps*em+wt*src**2/(4*eps)-s.sqrt(wt*em)*src
                      -(2*eps*s.sqrt(em)-s.sqrt(wt)*src)**2/(4*eps))==0
    print('PASS outgoing characteristic m0..6, lower-jet boundary squares, inner Pi6/Pi7 correction')


if __name__=='__main__':
    exact()
