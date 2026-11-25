"""Original fixed-window causal localization and absolute energy bound.
Uses existing W0 finite propagation, moving energy/lift and TT modal identities.
No signal sign or physical validation. All constants exact rational.
"""
from fractions import Fraction as Q
from math import comb,factorial
import json
from check_f8_fixed_window_causal_cap import run as cap


def run():
    geometry=cap(); eps=Q(1,25); pulse=Q(13,200); d=Q(7,20000)
    # Smooth one-sided convolution cutoffs: step * nine normalized boxes
    # * one nonnegative smooth unit-mass mollifier, each width 1/100000.
    # Radial cutoff rises from .0395 to .0396; time cutoff falls from
    # .00045 to .00050 (one box + mollifier, each width .000025).
    H=Q(1,2000); wr=Q(1,100000); wt=Q(1,40000)
    assert 10*wr==Q(1,10000) and 2*wt==Q(1,20000)
    assert Q(396,10000)-Q(395,10000)==10*wr
    assert Q(9,20000)+2*wt==H
    # e lower from positive Taylor terms; powers rounded DOWN in exponent.
    e=Q(2718,1000);assert sum((Q(1,factorial(j)) for j in range(8)),Q(0))>e
    ex=lambda n:e**(-n)
    # At real r=eps-delta, complex disk |z-r|<=delta/4:
    # Re[1/(eps-z)]>=4/(5 delta), Re[1/(eps+z)]>0.
    # 1/(1-z²/eps²)=eps/2*(1/(eps-z)+1/(eps+z)).
    # Cauchy derivative bound maximized at delta=H, since eps*2/(5H)=32>9.
    assert eps*Q(2,5)/H==32
    m=9;D=[Q(factorial(j))*(4/H)**j*ex(31) for j in range(m+1)]
    C=[sum((Q(comb(j,i))*D[i]*(2/wr)**(j-i) for i in range(j+1)),Q(0)) for j in range(m+1)]
    # |c_n| <= Csrc k^-9, 9 integrations by parts, sqrt(2/R)<1.
    # Compact smooth radial support away from both endpoints, all jets flat.
    Csrc=eps**4*H*(eps*C[m]+m*C[m-1])
    # temporal bump X>=pulse/(4 H)=32.5; |d bump/dT|<=4/pulse X² exp(1-X).
    X=pulse/(4*H);assert X>=32 and X>2
    a0=ex(31);a1=(4/pulse*X**2+2/wt)*a0
    # Existing characteristic lift ell=(amp/v)c_n(1-y/Y)e^-ky,
    # amp/v=6/b² times localized temporal bump. b>=1/2, |b'|<=1.
    A=24*a0;At=96*a0+24*a1
    # Source support H, weight <=8, k>=1,Y>1: forcing norm <=
    # 2 sqrt(k)(7 A+At)|c_n|. Existing norm rate <=5/2, span<2.8.
    # exp(7)<1200 by positive series+tail (same original energy owner).
    q=Q(7);s=sum((q**j/factorial(j) for j in range(40)),Q(0));assert s+q**40/factorial(40)/(1-q/41)<1200
    # Trace k|Uwall|²<=250 ||state||², sqrt(250)<16.
    Cwall=16*1200*H*2*(7*A+At)
    # Receiver original chi normalization >=1/15. X_w>=.05/d>142.
    # Source-free observer integration by parts done on ORIGINAL full window,
    # then restrict integrand by exact finite propagation, no cutoff derivatives.
    Xw=Q(1,20)/d;assert Xw>142 and Xw>4
    w0=15*ex(141);w1=20*Xw**2*w0;w2=100*(2*Xw**2+8*Xw**3+4*Xw**4)*w0
    # Existing original clock multiplier bounds: a2 coeff derivatives 1,3,9;
    # a1 coeff derivatives 2,7; a0 coeff <=1/2. Both E4 and SMS.
    W=d*(Q(33,2)*w0+8*w1+w2)
    # Original TT modal B_l = sqrt(2/R) k^5 c_l j_l(kr),
    # sum |c_l|=1, |j_l|<=1, k>=n; q includes at most k².
    assert Q(2,5)+Q(4,7)+Q(1,35)==1 and Q(333,106)>Q('3.012')
    # sum n^-2<=2 by integral test, no finite-prefix omission.
    bound=2*Csrc*Cwall*W
    # All signs lost only in this upper bound. No nonzero assertion.
    import sympy as S
    x,a,r=S.symbols('x a r',positive=True);assert S.cancel(1/(1-(r/a)**2)-a/2*(1/(a-r)+1/(a+r)))==0
    # Cauchy disk guard: Re(1/(delta+w))>=1/(delta+radius).
    u,v=S.symbols('u v',real=True);D0,R=S.symbols('D0 R',positive=True)
    assert S.expand((D0+u)*(D0+R)-((D0+u)**2+v*v)-((D0-R)*(R-u)+R*R-u*u-v*v))==0
    assert S.expand((S.diff(x**2*S.exp(-x),x)-x*(2-x)*S.exp(-x)))==0
    # Flat bump derivative expressions in dimensionless coordinate.
    t=S.symbols('t');z=1/(1-t*t);f=S.exp(1-z)
    assert S.simplify(S.diff(f,t)+2*t*z*z*f)==0
    assert S.simplify(S.diff(f,t,2)-(-2*z*z-8*t*t*z**3+4*t*t*z**4)*f)==0
    # exact decimal order; comparison not float underflow.
    n=0
    while bound<Q(1,10**(n+1)):n+=1
    assert n>20
    return dict(scope='conditional absolute bound for original continuous fixed-window scalar TT yy E4/SMS contraction; not sign, full curvature authority or physical result',geometry=geometry,radial_order=m,source_coefficient_upper=float(Csrc),wall_factor_upper=float(Cwall),receiver_factor_upper=float(W),bound_upper=float(bound),decimal_upper='1e-'+str(n),bound_rational=str(bound),symbolic_checks=5,notes='smooth one-sided cutoffs agree on causal support; source replacement only in proof, no retuning. Original full-window IBP precedes support restriction. No finite modal prefix required for absolute bound.')
if __name__=='__main__':print(json.dumps(run(),indent=2))
