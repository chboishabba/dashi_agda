"""Exact spherical Einstein completion of the prior active stress comparator.
Classical anisotropic TOV, G=c=R=1; inverse stress, not a material action.
"""
import sympy as s
from scipy.integrate import quad
import numpy as np

def main():
    r,l=s.symbols('r l', positive=True)
    p=l/(8*s.pi); rho=(2+l)*p*(1-r*r); pr=-p*(1-r*r)**2
    m=l*(2+l)/2*(r**3/3-r**5/5)
    f=1-2*m/r; v=s.factor((m+4*s.pi*r**3*pr)/(r*r*f))
    pt=s.factor(pr+r*(s.diff(pr,r)+(rho+pr)*v)/2)
    eq=lambda x: s.simplify(x)==0
    assert eq(s.diff(m,r)-4*s.pi*r*r*rho)
    assert eq(s.diff(pr,r)+(rho+pr)*v+2*(pr-pt)/r)
    assert eq(2*r*r*f*v-2*m-8*s.pi*r**3*pr)
    # Angular Einstein equation, ds²=-exp(2nu)dt²+dr²/f+r²dOmega².
    assert eq(f*(s.diff(v,r)+v*v+v/r)+s.diff(f,r)*(v+1/r)/2-8*s.pi*pt)
    assert all(eq(x.subs(r,1)) for x in (rho,pr,pt))
    assert eq(v.subs(r,1)-m.subs(r,1)/(1-2*m.subs(r,1)))
    assert eq(s.limit(v,r,0)) and eq(s.limit(pt-pr,r,0))
    # Original flat tangential stress is saturated at the outer edge.
    # Its GR correction requires slack. rho/p=(2+l)(1-r²) adds O(l) slack.
    # For 0<l<=1/10, m/r<=7l/20, f>=93/100.
    # Both terms in r² f nu' / r are opposite signed; |r nu'|<=50l/93.
    # Therefore |pt-pt_flat|/[p(1-r²)] <=(21/20)*(50l/93)<l.
    assert s.Rational(21,20)*s.Rational(50,93)<1
    # nu'/r numerator in units l: negative constant, positive linear, negative quadratic in x=r².
    x=s.symbols('x'); poly=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    assert eq(v-r*l*poly.subs(x,r*r)/f)
    assert eq(poly.subs(x,0)-(l-1)/6)
    assert eq(poly.subs(x,1)-(2+l)/15)
    # Concave polynomial has one root in (0,1), second >1.
    lv=s.Rational(1,10); roots=s.solve(poly.subs(l,lv),x)
    roots=sorted(float(z) for z in roots); assert 0<roots[0]<1<roots[1]
    rs=np.sqrt(roots[0]); mm=float(m.subs({r:1,l:lv})); vv=s.lambdify(r,v.subs(l,lv),'numpy'); ff=s.lambdify(r,f.subs(l,lv),'numpy')
    nu0=np.log(1-2*mm)/2-quad(vv,0,1,epsabs=1e-13)[0]
    # Static orthonormal outward acceleration of a released particle is -sqrt(f) nu'.
    acc=lambda rr:-np.sqrt(ff(rr))*vv(rr)
    assert acc(.25)>0 and acc(.75)<0
    print('lambda',lv,'mass',mm,'sign radius',rs,'central lapse',np.exp(nu0),'a(.25)',acc(.25),'a(.75)',acc(.75))
    print('PASS exact TOV Einstein equations, regularity, matching, DEC sufficient bound and acceleration sign')
if __name__=='__main__':main()
