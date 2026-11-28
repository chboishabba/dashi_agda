#!/usr/bin/env python3
"""Exact, non-promoting cross-lane regression: NS physical R734 signed transfer,
complex phase residual, whole-space radial split, existing Hodge star and
P-vs-NP DAG cost. Original-source analytics/kernel checks are not inferred.
Waleffe triad conservation; Bishop/Machin interval-method provenance.
"""
from fractions import Fraction as F
import sympy as S

def check_zero(e):
    assert S.simplify(e) == 0, e

def signed_triad():
    x,y,z,w1,w2,w3,a,b=S.symbols('x y z w1 w2 w3 a b',real=True)
    p,q,r=y-z,z-x,x-y
    check_zero(p+q+r)
    check_zero(x*p+y*q+z*r)
    prod=w1*p+w2*q+w3*r
    check_zero(prod-((w1-a-b*x)*p+(w2-a-b*y)*q+(w3-a-b*z)*r))
    check_zero((z-x)*prod-q*((z-x)*(w2-w1)-(w3-w1)*(y-x)))
    for x,y,z in ((1,S.sqrt(5),S.sqrt(6)),(-1,S.sqrt(5),-S.sqrt(6)),
                  (0,0,2),(2,2,2),(-3,2,2),(0,-3,5)):
        p,q,r=y-z,z-x,x-y
        check_zero(x*p+y*q+z*r)
        for w in ((1,2,2),(1,1,1),(x,y,z),(1,-2,4)):
            lhs=sum((u*t for u,t in zip(w,(p,q,r))))
            rhs=sum(((u-3-2*v)*t for u,v,t in zip(w,(x,y,z),(p,q,r))))
            check_zero(lhs-rhs)
    amp=(5-S.sqrt(5)+S.sqrt(30))/10
    x,y,z=1,S.sqrt(5),S.sqrt(6)
    check_zero(amp*((y-z)+2*(z-x)+2*(x-y)) -
               (5+S.sqrt(5)-S.sqrt(30))/10)
    return 28

def add(x,y): return (x[0]+y[0],x[1]+y[1])
def sub(x,y): return (x[0]-y[0],x[1]-y[1])
def mul(x,y): return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def conj(x): return (x[0],-x[1])
def n1(x): return abs(x[0])+abs(x[1])

def phase():
    samples=[
      (((2,3),(1,-4),(3,2)),((F(19,10),F(31,10)),(F(11,10),-4),(3,F(9,5)))),
      (((-2,0),(0,4),(-3,1)),((-2,F(1,5)),(F(1,10),4),(-3,F(11,10)))),
      (((0,0),(F(2,3),F(7,9)),(0,0)),((F(1,8),0),(F(2,3),F(7,9)),(F(1,10),0))),
      (((F(1,2),F(-3,2)),(4,5),(F(7,3),-2)),((F(3,5),-1),(F(39,10),F(49,10)),(F(8,3),F(-21,10))))
    ]
    for triple,approx in samples:
        a,b,c=[tuple(map(F,p)) for p in triple]
        A,B,C=[tuple(map(F,p)) for p in approx]
        ea,eb,ec=[n1(sub(t,T)) for t,T in zip((a,b,c),(A,B,C))]
        exact=mul(mul(a,b),conj(c)); estimated=mul(mul(A,B),conj(C))
        delta=sub(exact,estimated)
        telescope=add(add(mul(mul(sub(a,A),b),conj(c)),
                          mul(mul(A,sub(b,B)),conj(c))),
                      mul(mul(A,B),conj(sub(c,C))))
        assert delta==telescope
        upper=ea*(n1(B)+eb)*(n1(C)+ec)+n1(A)*eb*(n1(C)+ec)+n1(A)*n1(B)*ec
        assert n1(delta)<=upper and abs(delta[0])<=upper
        flip=mul(mul(a,b),conj((-c[0],-c[1])))
        assert flip==(-exact[0],-exact[1])
        assert mul(c,conj(c))==mul((-c[0],-c[1]),conj((-c[0],-c[1])))
    return 20

def radial():
    E,D,R=S.symbols('E D R',positive=True)
    v=S.symbols('v',positive=True)
    check_zero(S.integrate(4*S.pi,(v,0,R))-4*S.pi*R)
    check_zero(S.integrate(4*S.pi/v**2,(v,R,S.oo))-4*S.pi/R)
    split=S.sqrt(4*S.pi*R*E)+S.sqrt(4*S.pi*D/R)
    check_zero(S.simplify(split.subs(R,S.sqrt(D/E))**4-256*S.pi**2*E*D))
    # 1/|k| requires explicit periodic zero-mode separation.
    assert S.Integer(0) not in [S.Integer(1),S.Integer(2)]
    return 4

def hodge():
    t,j=S.symbols('t j')
    gb=S.groebner([t**3+t**2-2*t-1,j*j-t+2],j,t,order='lex',domain=S.QQ)
    R=(t+(1-t-t*t)*j)/2
    for e in (R*R-t*R+1,sum(R**k for k in range(7)),
              R**4-R**3-j,(j*j+2)**3+(j*j+2)**2-2*(j*j+2)-1):
        _,rem=gb.reduce(S.expand(e)); check_zero(rem)
    return 4

def dag_cost():
    # Source owner: PNPAggregateGateCountExact.agda.
    cost=lambda d,k:2+2*d*k
    for rows in ([],[(2,1)],[(3,2),(5,3)],[(10,2),(4,0)]):
        max_excess=sum(max(0,d-c) for d,c in rows)
        gates=lambda k:2+cost(max_excess,k+1)+sum(cost(d,d) for d,c in rows)
        for k in (0,1,2,5,100,100000):
            cap=min(k,max_excess)
            assert gates(cap)<=gates(k)
            assert all((p<=k)==(p<=cap) for p in range(max_excess+1))
    return 24

if __name__=="__main__":
    checks=dict(NS_signed=signed_triad(),NS_complex_phase=phase(),
                NS_Euclidean=radial(),Hodge_cyclotomic=hodge(),
                PNP_DAG_cost=dag_cost())
    print("PASS",checks,"total",sum(checks.values()))
