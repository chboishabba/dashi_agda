"""Exact characteristic flux and causal inverse algebra; local kernel regression."""
import json
from fractions import Fraction as Q
import sympy as S
import numpy as np
from scipy.special import j0,j1
from check_f8_causal_block_inverse import I,rat,grid,envelope,enclose,propagate

def check():
    A,B,x,k=S.symbols('A B x k',real=True);r=S.Function('r')(A,B);V=S.Function('V')(x+(A-B)/2);f=S.Function('f')(A,B)
    p=4*S.diff(r,A,B)+V*r
    flux=S.diff(2*S.diff(r,B)**2+V*r*r/2,A)+S.diff(2*S.diff(r,A)**2+V*r*r/2,B)
    assert S.simplify(flux-p*(S.diff(r,A)+S.diff(r,B)))==0
    assert S.simplify(S.diff(V,A)+S.diff(V,B))==0
    # q = a2'' - a1' - k² a0; verify b-clock differentiation independently.
    T=S.symbols('T');b=S.Function('b')(T);chi=S.Function('chi')(T);v=S.diff(b,T);a=S.diff(b,T,2);beta=S.sqrt(1+b*b)
    checks=2
    for sc,extra,sign in ((S.Rational(1,4),0,-1),(S.Rational(1,2),2,1)):
        p=b*b*(1+b*b);p1=(2*b+4*b**3)*v;p2=(2+12*b*b)*v*v+(2*b+4*b**3)*a
        r=-b**4/beta+extra*b*b*beta;rp=(-4*b**3/beta+b**5/beta**3+extra*(2*b*beta+b**3/beta))*v
        q=-sc*(p2*chi+2*p1*S.diff(chi,T)+p*S.diff(chi,T,2))+sc*(rp*chi+r*S.diff(chi,T))-k*k*sign*sc*b*b*chi
        assert S.simplify(q-(S.diff(-sc*p*chi,T,2)-S.diff(-sc*r*chi,T)-k*k*sign*sc*b*b*chi))==0;checks+=1
    # Exact causal inverse without global contraction.
    L=S.Matrix([[0,0,0],[-2,0,0],[3,-4,0]]);Id=S.eye(3);G=(Id-L).inv();assert G==Id+L+L*L;checks+=1
    H=S.Matrix([[S.Rational(1,4),0,0],[4,S.Rational(1,2),0],[6,7,S.Rational(1,3)]]);d=S.Matrix([1,2,3]);e=(Id-H).inv()*d
    assert max(sum(H[i,j] for j in range(3)) for i in range(3))>1 and min(e)>0;checks+=1
    for i in range(3):assert e[i]==(d[i]+sum(H[i,j]*e[j] for j in range(i)))/(1-H[i,i]);checks+=1
    # Decimal directed recurrence on literal dyadic input, independent exact oracle.
    h=np.array([[.25,0,0],[4,.5,0],[6,7,.25]]);d0=np.array([1.,2.,3.]);exact=(Id-S.Matrix(h.tolist()).applyfunc(lambda x:S.Rational(float(x)))).inv()*S.Matrix([1,2,3]);u=propagate(h,d0)
    for x,y in zip(u,exact):assert Q(x)>=Q(int(y.p),int(y.q));checks+=1
    # Constant auxiliary potential branch, independent Bessel diagnostic.
    xi=I(-1);h=1/128;V=1+15*13**2/4;r=grid(-1,1,h,40,40);f,v,q=envelope(r,xi,I(1),h);numeric=0
    for aa,bb in ((.031,.047),(.101,.093),(.17,.22),(.281,.197)):
        z=np.sqrt(V*aa*bb);ra=-j1(z)*V*bb/(2*z);rb=-j1(z)*V*aa/(2*z);true=[j0(z)/2,(ra+rb)/2,(ra-rb)/2]
        bounds=enclose(r,f,v,q,xi,I(1),h,I(aa),I(bb))
        for a,b in zip(bounds,true):assert a.l<=b<=a.h;numeric+=1
    return dict(symbolic_exact=checks,local_bessel_regressions=numeric,scope='exact identities and finite recurrence; numerical comparisons not proof by sampling')
if __name__=='__main__':print(json.dumps(check()))
