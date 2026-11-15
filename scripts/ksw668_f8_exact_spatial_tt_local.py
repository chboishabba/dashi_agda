#!/usr/bin/env python3
"""Original a=t compact local TT yy source in REAL space (x-axis).

Q=diag(0,1,-1), P=-I*Delta+grad grad. For any radial scalar f(r):
 Syy[f](r,0,0)=f''''+2*f'''/r-3*f''/r²+3*f'/r³.
This is an exact local 4th-order source operator, so compact spatial
support is PRESERVED, unlike its badly underresolved radial Fourier inverse.
No 5D wave evolution or physical detector claim.
"""
import json
import mpmath as mp
import sympy as s

def symbolic():
    x,y,z,a=s.symbols('x y z a',real=True,positive=True)
    f=s.exp(-a*(x*x+y*y+z*z))
    DX=lambda v:s.diff(v,x,2)
    DY=lambda v:s.diff(v,y,2)
    DZ=lambda v:s.diff(v,z,2)
    operator=(DX(DX(f))+s.Rational(1,2)*DX(DY(f))+
      s.Rational(3,2)*DX(DZ(f))-s.Rational(1,2)*DY(DZ(f))+
      s.Rational(1,2)*DZ(DZ(f)))
    r=s.symbols('r',positive=True)
    g=s.exp(-a*r*r)
    radial=(s.diff(g,r,4)+2*s.diff(g,r,3)/r-
            3*s.diff(g,r,2)/r**2+3*s.diff(g,r)/r**3)
    assert s.simplify(operator.subs({x:r,y:0,z:0})-radial)==0
    assert s.factor(radial/g)==8*a*a*(2*a*a*r**4-8*a*r*r+3)
    return dict(radial_TT_yy='f4+2*f3/r-3*f2/r²+3*f1/r³',
       symbolic_nontrivial_Gaussian_identity_pass=True,
       compact_source_local_order4=True)

def evaluate(eps=.024,r=None):
    if eps<=0:raise ValueError('positive compact radius')
    if r is None:r=eps/3
    if r<=0:raise ValueError('radial identity at positive radius only')
    if r>=eps:return dict(eps=eps,r=r,exact_TT_yy=0.,outside_source=True)
    mp.mp.dps=45
    e=mp.mpf(str(eps));t=mp.mpf(str(r))
    normalization=4*mp.pi*e**3*mp.quad(
      lambda u:u*u*mp.exp(-1/(1-u*u)),[0,1])
    f=lambda x:mp.exp(-1/(1-(x/e)**2))/normalization
    value=e**4*(mp.diff(f,t,4)+2*mp.diff(f,t,3)/t-
                 3*mp.diff(f,t,2)/t**2+3*mp.diff(f,t)/t**3)
    return dict(eps=eps,r=r,exact_TT_yy=float(value),outside_source=False)

def audit():
    return dict(symbolic=symbolic(),inside=evaluate(),
       outside=evaluate(r=1.8220210521210103),
       moving_AdS5_PDE_propagated=False,
       physical_Weyl_accepted=False)

if __name__=='__main__':print(json.dumps(audit(),indent=2))
