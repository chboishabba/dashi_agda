#!/usr/bin/env python3
"""KSW B4: gauge-invariant electric Weyl for original *manufactured* AdS5 TT wave.

Original a=t AdS5 background, r_g from Caldwell–Langlois Eq19.
FRW 4D Weyl is zero, so the first-order electric Weyl is gauge invariant.
This is NOT a retarded source-to-receiver signal or a detector observation.
"""
import json
import sympy as s
import mpmath as mp

def symbolic_weyl():
    eta,x=s.symbols('eta x',real=True)
    h=s.Function('h')(eta,x)
    # h_yy=+h, h_zz=-h, k along x. No assumption of 4D vacuum wave.
    R0y0y=-s.diff(h,eta,2)/2
    Ric_yy=(s.diff(h,eta,2)-s.diff(h,x,2))/2
    C0y0y=R0y0y+Ric_yy/2
    assert s.simplify(C0y0y+(s.diff(h,eta,2)+s.diff(h,x,2))/4)==0

def audit():
    symbolic_weyl()
    mp.mp.dps=50
    def Tb(t):
        return mp.asinh(t)-mp.sqrt(1+t*t)/t
    r=mp.sqrt((Tb(2)-Tb(1))**2-mp.mpf('.5')**2)
    def H(eta,x):
        t=mp.exp(eta)
        z=1/t
        return z*z*mp.besselj(2,z)*mp.cos(x-mp.sqrt(2)*(Tb(t)-Tb(1)))
    eta=mp.log(2)
    hh=mp.diff(lambda a:H(a,r),eta,2)
    xx=mp.diff(lambda x:H(eta,x),r,2)
    E=-(hh+xx)/16
    assert abs(E)>mp.mpf('1e-8')
    return dict(status='PASS nonzero gauge-invariant Weyl of pre-existing nonretarded AdS5 TT mode',
                receiver_comoving_r=float(r),receiver_brane_proper_t=2.,
                manufactured_plus_electric_Weyl=float(E),
                identity='E_plus=-(d_eta²+d_x²)H_plus/(4a²)',
                background_FRW_Weyl_zero=True,
                retarded_localized_source=False,observed_early_physical_signal=False)
if __name__=='__main__':
    print(json.dumps(audit(),indent=2,sort_keys=True))
