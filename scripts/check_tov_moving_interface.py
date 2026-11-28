"""Original TOV surface: moving level set, traction and Israel shape cancellation.
Fixed background identities only; no coupled coercivity claim.
"""
import sympy as s
r,l=s.symbols('r l',positive=True); e,phi,u,ur=s.symbols('e phi u ur',real=True)
x=r*r;p=l/(8*s.pi)
rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
f=1-l*(2+l)*(x/3-x*x/5)
P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
N=r*l*P/f
M=l*(2+l)/15; F=1-2*M/r; Nv=M/(r*r*F)
def eq(z): return s.cancel(z)==0
def at(z): return z.subs(r,1)
for z in (f-F,s.diff(f-F,r),N-Nv,s.diff(N-Nv,r)):
    assert eq(at(z))
# Mixed extrinsic curvature eigenvalues sqrt(f)*nu' and sqrt(f)/r.
# Compare derivatives by cancelling the common sqrt(f) at the surface.
for h,hv in ((N,Nv),(1/r,1/r)):
    assert eq(at(h-hv))
    assert eq(at(f*s.diff(h,r)+s.diff(f,r)*h/2-F*s.diff(hv,r)-s.diff(F,r)*hv/2))
print('PASS matched metric/normal jets and cancellation of common Israel shape transport')
# Surface R=1. Taylor coefficients on the moved surface, with independent material variation.
R=1+e*(phi+u)
assert s.diff(R**2,e).subs(e,0)==2*(phi+u)
d=(rho+pr)/(2*f)
# radial material flux proportional to d(R) times normal derivative of R.
flux1=at(s.diff(d,r))*(phi+u)
assert eq(flux1.subs(u,-phi))
assert not eq(flux1.subs({u:0,phi:1,l:s.Rational(1,10)}))
assert eq(at(pr)) and eq(at(s.diff(pr,r)))
print('PASS moving level-set kinematics and first-order normal material flux cancellation')
print('PASS radial pressure and radial pressure gradient vanish; no shell traction from shift')
# Nonzero density slope distinguishes background matching from linearized source matching.
assert eq(at(s.diff(rho,r))+2*(2+l)*p)
assert not eq(at(s.diff(rho,r)))
print('PASS density slope retained; independent wall trace estimate still required')
