"""Explicit sufficient continuum WINDOW tail conditional on smooth retarded reference.
No raw/direct Weyl or numerical normal/time error enclosure. No source fit.
"""
import json, math
from fractions import Fraction as Q
import sympy as s
import mpmath as mp


def check():
    u,z=s.symbols('u z',positive=True);f=s.exp(1-1/(1-u*u));P=s.Integer(1);odd=1
    # (u f)^(m)=u^odd P_m(1/(1-u²)) f.
    # Check recurrence on the actual source with exact first/second derivatives.
    P1=1+2*(z*z-z)*(-1);P2=2*z*z*(s.diff(P1,z)-P1)
    assert s.simplify(s.diff(u*f,u)-P1.subs(z,1/(1-u*u))*f)==0
    assert s.simplify(s.diff(u*f,u,2)-u*P2.subs(z,1/(1-u*u))*f)==0
    # Original window bump derivative, one positive-side turning point of f'.
    assert s.simplify(s.diff(f,u,2)-2*f/(1-u*u)**2*(2/(1-u*u)**2-6/(1-u*u)+3))==0
    # Exact sufficient constants: v_T<=1/2, 1-|v|>=1/4, source t<=2.
    t=s.symbols('t',positive=True);assert s.expand((1+t*t)**2-2*t**3-(t**2-t)**2)==t*t+1
    assert Q(3,2)*Q(1,4)<1 and Q(13,200)*Q(7,4)<1
    # e^7<1200: geometric remainder after term 32, exact rationals.
    a=sum(Q(7)**j/math.factorial(j) for j in range(33));rem=Q(7)**33/math.factorial(33)/(1-Q(7,34));assert a+rem<1200
    assert 16*6300*Q(13,200)*1200<8000000
    # Normalization Z>=2h/3, h=.1, |chi'| L1<=30, |chi''| L1<=2400.
    assert 9+6*30+2400+7+2*30<2700
    # Sum |c_l|=1; for kr>=20 all |j_l|<=2/(kr).
    assert 1+Q(45,20**2)+Q(105,20**4)+Q(10,20)+Q(105,20**3)<2
    assert Q(2,5)+Q(4,7)+Q(1,35)==1
    # For k>=100, (2700/k²+1/2)<1; R/pi<1.
    assert Q(2700,100**2)+Q(1,2)<1
    mp.iv.dps=35;iv=mp.iv;Ngrid=2048;cut=2032 # u=127/128; z>64
    us=[iv.mpf([i/Ngrid,(i+1)/Ngrid]) for i in range(cut)];zs=[1/(1-x*x) for x in us]
    ex=[iv.exp(1-z) for z in zs];results=[]
    for m in range(1,21):
        P=s.expand(P+2*(z*z-z)*(s.diff(P,z)-P) if odd else 2*z*z*(s.diff(P,z)-P));odd=1-odd
        if m<8 or m%2:continue
        coeff=[int(c) for c in s.Poly(P,z).all_coeffs()];deg=len(coeff)-1;assert deg<=2*m<64
        total=iv.mpf(0)
        for x,e in zip(zs,ex):
            v=iv.mpf(0)
            for c in coeff:v=v*x+c
            total+=abs(v)*e/Ngrid
        # For z>=64, z^j exp(1-z) decreases; interval tail bound with width 1/128.
        total+=sum(abs(c)*64**(deg-i) for i,c in enumerate(coeff))*iv.exp(-63)/128
        # Round the interval upper endpoint up to an integer with an extra unit.
        # mp.mpf conversion is at 60 decimal digits, exceeding interval precision.
        mp.mp.dps=60;D=int(mp.ceil(mp.mpf(total.b._mpi_[1])))+1
        # |c_n|<=eps^(6-m) D k^-m, |window_n|<=8e6 k^6 |c_n|.
        # R/pi<1 and sum_(n>N) n^(6-m)<=N^(7-m)/(m-7).
        def bound(n):return Q(8000000)*Q(1,25)**(6-m)*D*Q(n)**(7-m)/(m-7)
        lo,hi=100,100
        while bound(hi)>Q(1,10**9):hi*=2
        while hi-lo>1:
            mid=(hi+lo)//2
            if bound(mid)<=Q(1,10**9):hi=mid
            else:lo=mid
        results.append(dict(m=m,derivative_L1_upper=D,bound_N512=float(bound(512)),bound_N4096=float(bound(4096)),sufficient_N_1e_9=hi))
    return dict(conditional_wall_transfer_constant=8000000,window_p_L1_upper=2700,rows=results,scope='continuous fixed-window E4/SMS signed sum, smooth same-box reference, no finite modal normal/time or raw/direct estimate')

if __name__=='__main__':print(json.dumps(check(),indent=2))
