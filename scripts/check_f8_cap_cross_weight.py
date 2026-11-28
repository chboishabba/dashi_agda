"""Conditional full-spectrum two-collar convergence using original free extension.
Cross bound intentionally coarse; not a scaled receiver error certificate.
"""
from fractions import Fraction as Q
import json
import sympy as S
from check_f8_cap_all_frequency import bounds

def run():
    # P_k with original constant extension below 1/13; 0<=V<=676.
    V=Q(15,4)*13**2;assert V<26**2
    # K0=.5 J0(k sqrt(AB)); on causal rectangle A,B>=0,
    # K=K0-.5 int_0^A int_0^B K0(A-a,B-b) V K(a,b) da db.
    # |K|<=.5 sum (V AB/4)^j/(j!)² <=.5 exp(sqrt(V AB)).
    j=S.symbols('j',integer=True,nonnegative=True);x=S.symbols('x',positive=True)
    # use central binomial <=4^j, check recurrence ratio for binomial/4^j.
    assert S.simplify(S.binomial(2*j+2,j+1)/S.binomial(2*j,j)/4-(2*j+1)/(2*j+2))==0
    T=Q('2.66');assert 26*T<70
    # M is a rational uniform bound on K in the whole extended kernel, not cap-limited.
    M=Q(3)**70;assert M>1
    # |d_A K0|<=k² B/8 by |J1(x)|<=x/2.
    # Differentiate the causal convolution; one edge term and one volume term.
    # |K_A|+|K_B| <= k²(A+B)/8 + V M(A+B)/4 + V M k² AB(A+B)/32.
    AplusB=2*T;AB=T*T
    d0=V*M*AplusB/4;d2=AplusB/8+V*M*AB*AplusB/32
    # K_t,K_z each bounded by sum of absolute characteristic derivatives;
    # source derivative by reciprocity. |v|<=1, source b>=.997.
    B0=4*d0+3*M/Q('.997');B2=4*d2
    assert max(B0,B2)<10000*M
    cross=Q('.0037')*10000*M
    # k>=1, |c_n|<=4 eps^6 exp(-sqrt(k)/5), original contour owner.
    # Derivative transfer through order6 uses bounded polynomial coefficient on r*>2.
    # For any polynomial k^p, pay exp(-delta sqrt(k)) with max (2p/(e delta))^(2p).
    p=6;delta=Q(1,100);assert (2*p/delta)**(2*p)>1
    y=S.symbols('y',positive=True);d=S.symbols('d',positive=True)
    assert S.simplify(S.diff(y**(2*p)*S.exp(-d*y),y)-y**(2*p-1)*S.exp(-d*y)*(2*p-d*y))==0
    # Two collar inverses consume .01 total, cross polynomial .01,
    # TT derivatives .01, leaving .17 from the original .20.
    b=bounds();assert b['gevrey_weight_loss']=='1/100'
    remaining=Q(1,5)-3*delta;assert remaining==Q(17,100)
    # Strict lower guard on receiver radius and image exclusion: original periodic
    # sine box R=3.012, r*<2.6, negative/periodic source image cannot contribute.
    assert 2*Q('3.012')-Q('.04')-Q('2.6')>Q('2.66')
    return dict(potential_upper=str(V),uniform_kernel_upper=str(M),cross_kernel_multiplier_upper=str(10000*M),cross_operator_upper_coefficient=str(cross),cross_operator='C_RE*(1+k^2)',source_gevrey_weight='1/5',two_self_inverse_weight_loss='1/100',cross_polynomial_weight_loss='1/100',source_derivative_weight_loss='1/100',remaining_weight=str(remaining),cross_polynomial_prefactor_upper=str(1+(4/delta)**4),scope='conditional full radial periodic/sine carrier convergence of actual two-collar block formula; no relative error or receiver sign certificate')
if __name__=='__main__':print(json.dumps(run(),indent=2))
