"""Original frozen G3 axial holonomy and a conserved weak-field stress example.
Not evolving spacetime shortcut, global off-axis minimum, or nonlinear GR source.
Classical calibration/Laue/linearized Einstein identities.
"""
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp,quad
from scipy.optimize import brentq


def axial():
    e=.25; L=.5
    S=solve_ivp(lambda r,y:[y[1],-16*e*e*y[0]/(3*(1+r*r)**4)],(0,64),(0.,1.),rtol=2e-13,atol=2e-15,dense_output=True)
    assert S.success
    N=S.y[1,-1]
    def psi(z):
        r=abs(z);return S.sol(r)[0]/(r*N) if r>1e-7 else 1/N
    A=lambda z:2*e/(1+z*z)
    I=4*e*np.arctan(L)
    # Equal compact endpoints, zero winding. Other windings not inferred.
    q=brentq(lambda j:quad(lambda z:j/np.sqrt(psi(z)**2-j*j),-L,L,epsabs=1e-12)[0]-I,0,.99,xtol=1e-14)
    wp=lambda z:q/np.sqrt(psi(z)**2-q*q)-A(z)
    closure=quad(wp,-L,L,epsabs=1e-12)[0]
    opt=quad(lambda z:psi(z)**2/np.sqrt(psi(z)**2-q*q),-L,L,epsabs=1e-12)[0]
    graph=quad(lambda z:psi(z)*np.sqrt(1+A(z)**2),-L,L,epsabs=1e-12)[0]
    horizontal=quad(psi,-L,L,epsabs=1e-12)[0]
    # Exact calibration form: omega=q dw + (sqrt(psi^2-q^2)+q A) dz.
    # Closed, dual norm 1, saturates proposed curve, for |q|<1<=psi.
    cal=quad(lambda z:np.sqrt(psi(z)**2-q*q)+q*A(z),-L,L,epsabs=1e-12)[0]
    assert abs(closure)<1e-11 and abs(cal-opt)<1e-11 and horizontal<opt<graph
    assert opt>=np.hypot(2*L,I) # psi>=1 on original normalized real source
    print('axial holonomy',I,'momentum',q,'closure',closure,'horizontal wrong endpoint',horizontal,'same-endpoint optimum',opt,'fixed graph',graph,'calibration',cal)


def active():
    r=s.symbols('r',nonnegative=True);p=s.symbols('p',positive=True)
    rho=2*p*(1-r*r);pr=-p*(1-r*r)**2;pt=pr+r*s.diff(pr,r)/2
    assert s.simplify(s.diff(pr,r)+2*(pr-pt)/r)==0
    assert all(s.simplify(v.subs(r,1))==0 for v in (rho,pr,pt))
    # On 0<=r<=1, rho>=|pr|,|pt| since |1-r²|<=1 and |-1+3r²|<=2.
    act=s.factor(rho+pr+2*pt)
    assert s.simplify(act-p*(1-r*r)*(7*r*r-1))==0
    assert s.integrate((pr+2*pt)*r*r,(r,0,1))==0
    u=s.symbols('u',nonnegative=True)
    m=s.integrate((act*r*r).subs(r,u),(u,0,r))
    assert s.simplify(m-p*(-r**3/3+8*r**5/5-r**7))==0
    assert m.subs(r,1)==s.integrate(rho*r*r,(r,0,1))==4*p/15
    root=s.sqrt(s.Rational(4,5)-s.sqrt(s.Rational(23,75)))
    assert s.simplify(m.subs(r,root))==0
    # Actual acceleration in weak static linearization is -4 pi G*m/r² in c=1 units.
    # Positive outside gravitational mass; negative inner enclosed active density.
    print('active density',act,'enclosed active mass/(4pi)',m,'sign reversal radius',root.evalf(14),'total energy/(4pi)',m.subs(r,1))
    print('PASS conserved flat stress, dominant-energy sufficient bounds by factors, Laue integral and local/exterior sign')

if __name__=='__main__':
    axial();active()
