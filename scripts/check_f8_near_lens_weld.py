"""Original t12 near lens, within the fixed compact source spacetime tube.
Rational geometry and exact principal symbols, not a fixed-bump nonzero proof.
"""
from fractions import Fraction as F
import json
import sympy as s
from check_f8_causal_rk3_weld import sqrt_bounds,log_bounds
from check_f8_patch_causal import elapsed


def check():
    tr=F(12);te=F(201,200);eps=F(1,25);pulse=F(13,200)
    Tlo,Thi=elapsed(tr,F(1));elo,ehi=elapsed(te,F(1));lo,hi=elapsed(tr,te)
    assert 0<elo<=ehi<pulse
    # The receiving radius is fixed by the original t1 point cone minus .012.
    b0=1-1/tr;bl,bh=sqrt_bounds(Tlo*Tlo-b0*b0)[0],sqrt_bounds(Thi*Thi-b0*b0)[1]
    rl,rh=bl-F(3,250),bh-F(3,250)
    dz=1/tr-1/te
    xl,xh=sqrt_bounds(lo*lo-dz*dz)[0],sqrt_bounds(hi*hi-dz*dz)[1]
    el,eh=rl-xh,rh-xl
    assert -eps<el<=eh<eps
    margin=rl-eps-log_bounds(tr)[1];assert margin>0
    # Null chord slope is negative. At emission v_e < slope < v_r at reception.
    ql,qh=dz/lo,dz/hi
    ae,be=sqrt_bounds(1+te*te);ar,br=sqrt_bounds(1+tr*tr)
    gap_e=ql+1/be;gap_r=-1/ar-qh
    assert min(gap_e,gap_r)>0
    t=s.symbols('t',positive=True);q=s.symbols('q',real=True)
    # b(T)=1/t; b_T=-1/sqrt(1+t²), T_t=sqrt(1+t²)/t².
    assert s.simplify(s.diff(-1/s.sqrt(1+t*t),t)/(s.sqrt(1+t*t)/t**2)-t**3/(1+t*t)**2)==0
    omega=(s.sqrt(1+t*t)+q)/t; k2=1-q*q
    assert s.simplify(omega**2-k2-(1+q*s.sqrt(1+t*t))**2/t**2)==0
    # E4 principal multiplier = (omega_eta²+k_x²)/(4t²),
    # SMS = (omega_eta²-k_x²)/(2t²); q-v_r !=0 gives second strictly positive.
    # Direct E5 equals SMS on the original exact source-free wall/bulk solution.
    def pair(a,b):return [float(a),float(b)]
    return dict(te=float(te),tr=float(tr),emission_elapsed=pair(elo,ehi),receiver_radius=pair(rl,rh),emitter_x=pair(el,eh),photon_dark_margin_lower=float(margin),chord_slope=pair(ql,qh),emission_transverse_gap_lower=float(gap_e),receiver_transverse_gap_lower=float(gap_r),strict_convexity=True,principal_e4_positive=True,principal_sms_positive=True,fixed_original_bump_nonzero_proved=False)

if __name__=='__main__':print(json.dumps(check(),indent=2))
