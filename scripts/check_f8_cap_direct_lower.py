"""Exact lower magnitude for original E4 direct cap, no full inverse sign."""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,ceil
import json
import sympy as S
from check_f8_cap_all_frequency import clock,root
from check_f8_global_wall_kernel import Fbox

def run():
    f=Fbox(Q(1));g=Fbox(Q(1,12));span=(g[0]-f[1],g[1]-f[0]);T=(span[0]-Q(1,20),span[1]-Q(1,20));eps=Q('.04');pulse=Q('.065')
    r=(root(span[0]**2-Q(11,12)**2)[0]-Q('.012'),root(span[1]**2-Q(11,12)**2)[1]-Q('.012'));assert 2<r[0]<r[1]<3
    step=Q(1,10**6);ss=[j*step for j in range(96,117)];dd=[j*step for j in range(149,180)]
    bs=[clock(s,f) for s in ss];br=[(clock(T[1]-d,f)[0],clock(T[0]-d,f)[1]) for d in dd]
    assert min(x[0] for x in br)>Q('.0875') and Q('.0875')**3>Q('.025')**2
    # original window normalization <=.2; amplitude and conjugation prefactor
    # 6/(pi bs^(5/2) sqrt(1+bs²)) >=14/11; A>=17/32.
    pref=Q(14,11)*Q('.025')*Q(17,32)*5
    e=Q('2.71828183');v=sum((Q(1,factorial(j)) for j in range(13)),Q(0));assert v+Q(1,factorial(13))/(1-Q(1,14))<e
    @lru_cache(None)
    def exp_lower(n):return e**(-n)
    X,Y=S.symbols('X Y');P=S.Integer(1);p=1;polys=[]
    for j in range(7):
        c=S.Poly(S.expand((-1)**j*P.subs(X,Y+50)),Y);assert min(c.all_coeffs())>0;polys.append([int(a) for a in c.all_coeffs()]);P=S.expand(P+2*(X*X-X)*(S.diff(P,X)-P) if p else 2*X*X*(S.diff(P,X)-P));p=1-p
    def poly(j,x):
        out=Q(0)
        for c in polys[j]:out=out*(x-50)+c
        return out
    Xs=lambda s:1/(1-(2*s/pulse-1)**2);Xw=lambda d:1/(1-(1-10*d)**2);Xr=lambda a:1/(1-(1-a/eps)**2)
    scale=10**300;total=0;cells=0;largest=0
    for i in range(len(ss)-1):
        s0,s1=ss[i:i+2]
        for j in range(len(dd)-1):
            d0,d1=dd[j:j+2];bs0,bs1=bs[i:i+2];br0,br1=br[j:j+2]
            D2lo=(T[0]-d1-s1)**2-(bs1[1]-br1[0])**2
            D2hi=(T[1]-d0-s0)**2-(bs0[0]-br0[1])**2
            alo=root(D2lo)[0]-r[1]+eps
            # Interior radial strips immediately behind earliest light cone.
            for l in range(1,13):
                a1=alo-Q(l,4)*step;a0=a1-step/4
                if a0<=0:continue
                qlo=D2lo-(r[1]-eps+a1)**2;qhi=D2hi-(r[0]-eps+a0)**2
                assert 0<qlo<=qhi
                Xmin=Xr(a1);assert Xmin>50 and a1<eps/100
                # j=4,6 positive terms alone, all others reinforce E4.
                radial4=eps**1*Q('.99')*poly(4,Xmin)/r[1]
                radial6=eps**(-1)*Q('.99')*poly(6,Xmin)/r[1]
                wmin=Xw(d1);wmax=Xw(d0);umin=1-10*d1
                w2=100*(4*umin**2*wmin**4*(1-2/wmin)-2*wmax**2);assert w2>0
                receiver=(Q('.0875')**2/4)*(w2*radial4+radial6)
                exponent=ceil(Xs(s0)+Xw(d0)+Xr(a0)-3)
                low=pref*receiver*exp_lower(exponent)*(s1-s0)*(d1-d0)*(a1-a0)/root(qhi)[1]
                units=(low.numerator*scale)//low.denominator;total+=units;cells+=1;largest=max(largest,units)
    bound=Q(total,scale);assert bound>Q(1,10**270)
    return dict(cells=cells,source_tiles=len(ss)-1,receiver_tiles=len(dd)-1,radial_strips=12,lower_display=float(bound),exact_lower_numerator=str(total),exact_lower_denominator='1e300',strict_lower='1e-270',largest_tile_display=float(Q(largest,scale)),scope='E4 direct magnitude lower from disjoint positive rational subtiles; first correction reinforces under prior sign hypothesis; no full receiver sign')
if __name__=='__main__':print(json.dumps(run(),indent=2))
