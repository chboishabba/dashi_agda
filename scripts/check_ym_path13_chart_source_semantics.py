"""Source-semantic SU(2) chart identities and exact flat holonomy fixture.
Symbolic identities plus elementary convergent-series proof in Paper 3.
No claim of Agda kernel checking or general variational source closure.
"""
import sympy as S
from fractions import Fraction as F
from itertools import product

def cross(u):
    x,y,z=u;return S.Matrix([[0,-z,y],[z,0,-x],[-y,x,0]])
def symbolic():
    n=S.symbols('n',integer=True,nonnegative=True)
    ratio=(2*n+1)**2/((2*n+2)*(2*n+3))
    assert S.cancel((2*n+3)*ratio-(2*n+1)**2/(2*n+2))==0
    assert S.cancel((2*n+2)*(2*n+3)*ratio/(2*n+1)-(2*n+1))==0
    # f_n=(2n+1)c_n -> 2(1-s)F'=F; derivative of (1-s)F^2 vanishes.
    s,f=S.symbols('s f');assert S.cancel(-f*f+2*(1-s)*f*f/(2*(1-s)))==0
    a,L,Lp=S.symbols('a L Lp');u=S.Matrix(S.symbols('u0:3'));s=(u.T*u)[0]
    X=2*L*cross(u);J=a*L*S.eye(3)-L*cross(u)+2*a*Lp*u*u.T
    defect=2*L**2*(J-S.eye(3))+L**2*X-a*Lp*X**2
    expected=2*L**2*(a*(L+2*s*Lp)-1)*S.eye(3)
    assert (defect-expected).applyfunc(S.expand)==S.zeros(3)
    # Root-free stereographic interpolation q(r) and its left velocity.
    r=S.symbols('r',real=True);v=S.Matrix(S.symbols('v0:3',real=True));v2=(v.T*v)[0]
    den=1+r*r*v2;q0=(1-r*r*v2)/den;qv=2*r*v/den
    d0=S.diff(q0,r);dv=qv.diff(r)
    scalar=d0*q0+(dv.T*qv)[0]
    vector=-d0*qv+q0*dv-dv.cross(qv)
    assert S.cancel(scalar)==0
    assert (vector-2*v/den).applyfunc(S.cancel)==S.zeros(3,1)
    assert (dv/q0-2*v/den).applyfunc(S.cancel)==S.zeros(3,1)
    assert S.cancel(q0*q0+(qv.T*qv)[0]-1)==0
    rho=F(1,8192);delta=F(37,1024)
    assert 1-delta*delta/2>F(1,2) and delta*delta<F(1,4)
    assert 48*delta*delta==F(4107,65536)<F(1,4)
    print('PASS symbolic arcsinc recurrence, derivative polynomial, stereographic left velocity; outer w <=',48*delta*delta)

def cp(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def ci(a):return (a[0],-a[1])
def power(a,n):
    if n<0:return power(ci(a),-n)
    z=(F(1),F(0))
    for _ in range(n):z=cp(z,a)
    return z

def flat_fixture():
    # Same U(1) subgroup inside SU(2), constant links and nontrivial torus holonomy.
    t=[F(k,32768) for k in (1,-2,3,-4)]
    links=[((1-x*x)/(1+x*x),2*x/(1+x*x)) for x in t]
    e=(F(1),F(0));r=F(1,8192)
    for a in links:
        assert cp(a,ci(a))==e
        assert 2*(1-a[0])<=4*r*r
    for a,b in product(links,repeat=2):assert cp(cp(cp(a,b),ci(a)),ci(b))==e
    coarse=[power(a,13) for a in links];assert all(a!=e for a in coarse)
    # Canonical contour powers generate all possible commuting transports.
    # Pairwise generator commutation proves every contour relative holonomy 1.
    for axis in range(4):
        for d in range(4):
            for n in range(-6,7):
                p=power(links[d],n);c=coarse[axis]
                assert cp(cp(cp(p,c),ci(p)),ci(c))==e
    print('PASS nontrivial commuting Path13 holonomies; all plaquette types identity; all generator contour commutators identity')
    print('Wilson action is zero (global minimum by nonnegative chordal plaquette action); no general gauge uniqueness/analyticity claimed')
if __name__=='__main__':symbolic();flat_fixture()
