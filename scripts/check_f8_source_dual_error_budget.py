"""Exact rational source-only cubic interpolation/nodal error coefficients.
Conditional on a C4 continuum dual g(x), x=(r/eps)^2, and nodal error bounds.
Not an enclosure of either the continuum dual or native propagation.
"""
from fractions import Fraction as F
from pathlib import Path
import json,math
import sympy as S

POLYS=((6,81,-92,-46,70,-15),(6,54,-109,58,-7),(24,-36,12,1))
SCALES=(F(8,5),F(32,7),F(16,35))
EPS=F(1,25);UNIT=10**80


def profile_checks():
    u=S.symbols('u',positive=True);logf=1-1/(1-u*u);der=[S.Integer(1)]
    for j in range(4):der.append(S.cancel(S.diff(der[-1],u)+S.diff(logf,u)*der[-1]))
    old=(S.Rational(2,5)*(der[4]+4*der[3]/u),S.Rational(4,7)*(der[4]+der[3]/u-6*der[2]/u**2+6*der[1]/u**3)/u**2,S.Rational(1,35)*(der[4]-6*der[3]/u+15*der[2]/u**2-15*der[1]/u**3)/u**4)
    for i,p in enumerate(POLYS):
        q=sum(c*u**(2*(len(p)-j-1)) for j,c in enumerate(p))
        assert S.cancel(old[i]*(1-u*u)**8-S.Rational(SCALES[i].numerator,SCALES[i].denominator)*q)==0
    return 3


def poly_interval(p,a,b):
    lo=hi=F(p[0]);a=a*a;b=b*b
    for c in p[1:]:
        w=(lo*a,lo*b,hi*a,hi*b);lo=min(w)+c;hi=max(w)+c
    return max(abs(lo),abs(hi))


def source_bound(i,a,b):
    # y^8 exp(1-y) peaks at y=8. Bound exp(y-1) below by 33 terms.
    lo=1/(1-a*a);hi=None if b==1 else 1/(1-b*b)
    y=lo if lo>=8 else (hi if hi is not None and hi<=8 else F(8))
    assert y>=1
    t=F(1);lower=t
    for k in range(1,33):t*= (y-1)/k;lower+=t
    return SCALES[i]*poly_interval(POLYS[i],a,b)*y**8/lower


def ceil_units(x):
    assert x>=0
    return -((-x.numerator*UNIT)//x.denominator)


def budget(dr,i,subdiv=16):
    h=dr/EPS;n=math.ceil(1/h)+1;d=3+4*i;x=[(j*h)**2 for j in range(n)];m4=0;mu=[0]*n
    for j in range(n-1):
        a=j*h;b=min(F(1),(j+1)*h);start=max(0,min(j-1,n-4));ids=list(range(start,start+4))
        for k in range(subdiv):
            c=a+(b-a)*k/subdiv;e=a+(b-a)*(k+1)/subdiv
            g=EPS**d*(e**d-c**d)/d*source_bound(i,c,e)
            distances={l:max(abs(c*c-x[l]),abs(e*e-x[l])) for l in ids}
            m4+=ceil_units(g*math.prod(distances.values())/24)
            for l in ids:
                mu[l]+=ceil_units(g*math.prod(distances[m]/abs(x[l]-x[m]) for m in ids if m!=l))
    return dict(d=d,source_interpolation_M4_coefficient_upper=str(F(m4,UNIT)),nodal_coefficients_upper=[str(F(v,UNIT)) for v in mu],M4_float=float(F(m4,UNIT)),uniform_nodal_float=float(F(sum(mu),UNIT)))


def main():
    out=dict(scope='exact rational upper coefficients for source-only error, conditional on C4 continuum dual and independently enclosed nodal errors; no native propagation or sign certificate',exact_profile_checks=profile_checks(),subdivisions_per_source_interval=16,rows={})
    for dr in (F(1,125),F(3,500)):
        out['rows'][str(dr)]=[budget(dr,i) for i in range(3)]
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
