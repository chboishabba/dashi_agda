"""Strict direct single-layer E4 sign on actual cap, not the full wall inverse."""
from fractions import Fraction as Q
from math import factorial
import json
from check_f8_global_wall_kernel import Fbox
from check_f8_fixed_window_causal_cap import root, sub, shift, bracket
from check_f8_cap_radial_signed import run as signed

def run():
    sign=signed();f=Fbox(Q(1));span=sub(Fbox(Q(1,12)),f);end=shift(span,-Q(1,20))
    rlo=root(span[0]**2-Q(11,12)**2)[0]-Q(3,250);rhi=root(span[1]**2-Q(11,12)**2)[1]-Q(3,250)
    eps=Q(1,25);pulse=Q(13,200);s0,s1=Q(103,10**6),Q(104,10**6);d0,d1=Q(158,10**6),Q(159,10**6);a0,a1=s0,s1
    bs=bracket(shift(f,s1),'.999926462246','.999926462249');br=bracket(shift(Fbox(Q(1,12)),-Q(1,20)-d1),'.087603895134','.087603895138')
    # Monotonic radial reach in source/receiver times; worst delta is a1.
    gap=(end[0]-d1-s1)**2-(bs[1]-br[0])**2-(rhi-eps+a1)**2
    assert gap>0 and rhi<3 and rlo>Q('2.5')
    Xs=1/(1-(2*s0/pulse-1)**2);Xw=1/(1-(1-10*d0)**2);Xr=1/(1-(1-a0/eps)**2)
    assert Xs+Xw+Xr<670
    # e < 11/4 by sum and geometric tail; raw product > (4/11)^667.
    v=sum((Q(1,factorial(j)) for j in range(8)),Q(0));assert v+Q(1,factorial(8))/(1-Q(1,9))<Q(11,4)
    raw=Q(4,11)**667;assert raw>Q(1,10**294)
    # G_1 >= (17/32)/(2 pi sqrt(Q)) > 1 on this interior tile.
    assert Q(361,200000)<Q(43,1000)**2 and Q(17,32)>2*Q(22,7)*Q(43,1000)
    # a0 E4 magnitude >= b_r²/4 times raw window (normalization <1).
    # D W_rr term j=6 alone: 1/r* eps^-1 u P6(X) exp(1-Xr).
    # Other radial terms and p contribution share the sign on the entire cap.
    P6=Q(sign['radial_derivative_signs'][6]['constant']);radial=Q(1,3)/eps*Q(99,100)*P6
    assert Q('.08')**3>Q('.02')**2 and br[0]>Q('.08')
    # |amp|>4, b_s^-3/2>=1; direct trace -2 G g and W=b_r^3/2 F.
    # Original a0=-b² chi/4, normalized chi >= raw bump.
    pref=2*4*Q('.02')*Q('.08')**2/4*radial*(s1-s0)*(d1-d0)*(a1-a0)
    assert pref>10 and pref*raw>Q(1,10**293)
    return dict(scope='strict negative E4 direct single-layer term only; actual wall correction not included or sign-bounded',tile=dict(s=[float(s0),float(s1)],d=[float(d0),float(d1)],delta=[float(a0),float(a1)]),q_lower=float(gap),exponent_sum_upper=float(Xs+Xw+Xr),prefactor_lower=float(pref),direct_magnitude_strict_lower='1e-293',direct_sign='negative',full_receiver_sign_proved=False)
if __name__=='__main__':print(json.dumps(run(),indent=2))
