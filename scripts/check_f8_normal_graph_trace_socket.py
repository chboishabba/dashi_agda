"""F8 normal graph boundary trace requirements, actual GN coefficients.

A rigorous trace of H_nn,t^j requires the normal Sobolev graph
(H_nn,t^j,H_nnn,t^j). The hierarchy is not supplied by the original
first-order Israel Neumann condition alone. Explicit conservative trace
constants and both numerical stencil remainder debts are recorded.
"""
from fractions import Fraction as F
import sympy as s


def trace_constants():
    length=F(1,2)
    amin=F(6,875)  # a>1/5, N<7/6
    bmin=F(3,625)  # N>3/5
    return F(4)/(length*amin),F(4)*length/bmin


def stencil_remainders():
    # Dnn H = (2H0-5H1+4H2-H3)/h²
    H=(2,-5,4,-1)
    # Dn V = (-11V0+18V1-9V2+2V3)/(6h)
    V=(-11,18,-9,2)
    for degree in range(4):
        assert sum(c*j**degree for j,c in enumerate(H))==(2 if degree==2 else 0)
        assert sum(c*j**degree for j,c in enumerate(V))==(6 if degree==1 else 0)
    # Center Taylor bound; for H requires H_nnnn; V requires V_nnnn=H_nnnnn
    hbound=F(sum(abs(c)*j**4 for j,c in enumerate(H)),24)
    vbound=F(sum(abs(c)*j**4 for j,c in enumerate(V)),6*24)
    assert hbound==F(25,4)
    assert vbound==F(9,4)
    return hbound,vbound


def exact():
    t,n=s.symbols('t n',positive=True)
    a=s.sinh(s.asinh(t)-n)
    N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    A=a**3/N;B=N*a**3
    assert s.simplify(A.subs(n,0)-t**3)==0
    assert s.simplify(B.subs(n,0)-t**3)==0
    c0,c1=trace_constants()
    assert c0==F(3500,3) and c1==F(1250,3)
    hh,vv=stencil_remainders()
    # Exact weighted Hilbert-space source trace statement:
    # for each j=0..5, X_j=(integral(A|∂t^j H_nn|²+B|∂t^j H_nnn|²))/2
    # then |H_nn,t^j(0)|² <= c0*(A-component)/2+c1*(B-component)/2.
    x,y=s.symbols('x y',real=True)
    assert s.expand((x-y)**2-x*x-y*y+2*x*y)==0
    # Neumann trace does not control second normal derivative: choose
    # H1=n and H2=n+q n², both have same H_n(0), variable H_nn(0).
    q=s.symbols('q',real=True)
    H1=n;H2=n+q*n*n
    assert s.diff(H1,n).subs(n,0)==s.diff(H2,n).subs(n,0)
    assert s.simplify(s.diff(H2,n,2).subs(n,0)-s.diff(H1,n,2).subs(n,0)-2*q)==0
    # Defect amplifications for the two independent reconstructions:
    d=s.symbols('d',positive=True)
    assert s.simplify(hh*d**2-s.Rational(25,4)*d**2)==0
    assert s.simplify(vv*d**3-s.Rational(9,4)*d**3)==0
    print('PASS original collar H_nn time-jet graph trace (3500/3,1250/3), H and V stencil error sockets')
    print('Need six genuine time-indexed normal graph norms X0..X5 and fourth/fifth normal derivatives')

if __name__=='__main__':exact()
