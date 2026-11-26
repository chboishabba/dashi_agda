"""Original mode3 parity trace, FV regularity and fixed-window weak readout.
Exact algebra plus numerical source diagnostics, not production or kernel proof.
"""
import json
from fractions import Fraction as Q
import numpy as np
import sympy as S


def exact():
    count=0
    def check(x):
        nonlocal count
        assert x
        count+=1
    v,dp,dm,F,sp,sm=S.symbols('v dp dm F sp sm')
    check(S.expand(((1+v)*dp+F+sp-((v-1)*dm+F+sm))/2-((1+v)*dp+(1-v)*dm)/2-(sp-sm)/2)==0)
    # Interior Q is preserved by every affine RK stage, independently of v.
    q=S.symbols('q');check(S.expand(S.Rational(3,4)*q+q/4-q)==0)
    check(S.expand(q/3+2*q/3-q)==0)
    # Parity chain identity (vector-valued, applies to any radial power).
    for n in range(2,17):
        x=S.symbols('x:'+str(n+1));h=S.symbols('h',positive=True)
        m=n//2
        for j in range(m+1):
            check(S.cancel(sum((x[2*i+2]-x[2*i])/(2*h)*2*h for i in range(j))-(x[2*j]-x[0]))==0)
        check(Q(1,m+1)<=Q(2,n))
    # Radial FV quadratic exactness and source shell-average chart.
    e=S.symbols('e',real=True)
    for d in (3,7,11):
        den=((1+e/2)**d-(1-e/2)**d)/e
        p=d*(1+e/2)**(d-1)/den;m=d*(1-e/2)**(d-1)/den
        check(S.series(p+m,e,0,2).removeO()==2)
        check(S.series(p-m,e,0,3).removeO()==(d-1)*e)
        # exact weighted first two centered moments divided by radius powers
        t=S.symbols('t');D=S.integrate((1+e*t)**(d-1),(t,-S.Rational(1,2),S.Rational(1,2)))
        M1=S.integrate(t*(1+e*t)**(d-1),(t,-S.Rational(1,2),S.Rational(1,2)))/D
        M2=S.integrate(t*t*(1+e*t)**(d-1),(t,-S.Rational(1,2),S.Rational(1,2)))/D
        check(S.series(M1,e,0,3).removeO()==(d-1)*e/12)
        check(S.series(M2,e,0,2).removeO()==S.Rational(1,12))
    # Exact origin obstruction: K^2 of cell averages of r^2, unit spacing.
    def avg2(j,d):
        lo=max(Q(0),Q(j)-Q(1,2));hi=Q(j)+Q(1,2)
        return Q(d,d+2)*(hi**(d+2)-lo**(d+2))/(hi**d-lo**d)
    def Krow(j,d,x):
        if j==0:return 2*d*(x[0]-x[1])
        lo=Q(j)-Q(1,2);hi=Q(j)+Q(1,2);den=hi**d-lo**d
        return d*(hi**(d-1)*(x[j]-x[j+1])+lo**(d-1)*(x[j]-x[j-1]))/den
    x=[avg2(j,3) for j in range(3)];k=[Krow(j,3,x) for j in range(2)];obstruction=Krow(0,3,k)
    check(obstruction!=0)
    u=S.symbols('u');f=S.exp(1-1/(1-u*u));series=S.series(f,u,0,8).removeO()
    coeff=S.expand(S.Rational(2,5)*(S.diff(series,u,4)+4*S.diff(series,u,3)/u)).coeff(u,2)
    check(coeff==-56)
    # Physical clock adjoint coefficients, sign retained for each receiver.
    T=S.symbols('T');b=S.Function('b')(T);w=S.Function('w')(T);U=S.Function('U')(T)
    A=b*b*(1+b*b);beta=S.sqrt(1+b*b)
    for fac,extra,sign in ((S.Rational(1,4),0,-1),(S.Rational(1,2),2,1)):
        B=-b**4/beta+extra*b*b*beta
        a2=-fac*w*A;a1=-fac*w*B
        q=S.diff(a2,T,2)-S.diff(a1,T)
        check(S.expand(a2*S.diff(U,T,2)+a1*S.diff(U,T)-q*U-S.diff(a2*S.diff(U,T)-S.diff(a2,T)*U+a1*U,T))==0)
        check(sign in (-1,1))
    return dict(exact_checks=count,origin_K2_quadratic=str(obstruction),original_d3_source_quadratic=str(coeff),origin_K2_weighted_norm_lower_scaling='h^(-1/2)')


def source_diagnostics():
    # Dimensionless u=r/eps; fixed eps only multiplies powers by constants.
    x=S.symbols('x');f=S.exp(1-1/(1-x));J=lambda g:2*S.diff(g,x)
    lap=lambda g:4*x*S.diff(g,x,2)+6*S.diff(g,x)
    forms=[S.Rational(2,5)*lap(lap(f)),S.Rational(4,7)*J(J(lap(f))),S.Rational(1,35)*J(J(J(J(f))))]
    nodes,weights=np.polynomial.legendre.leggauss(64);rows=[]
    for d,form in zip((3,7,11),forms):
        # Evaluate only on support; a stable polynomial times exponential.
        fun=S.lambdify(x,S.factor(form),'numpy')
        for n in (64,128,256,512,1024,2048):
            h=1/n;j=np.arange(2*n);r=j*h;lo=np.maximum(0,r-h/2);hi=r+h/2;V=(hi**d-lo**d)/d
            end=np.minimum(hi,1);mask=end>lo;rr=lo[mask,None]+(end[mask]-lo[mask])[:,None]*(nodes+1)/2
            src=np.zeros(len(j));src[mask]=np.sum(weights*rr**(d-1)*fun(rr*rr),axis=1)*(end[mask]-lo[mask])/2/V[mask]
            cp=hi**(d-1)/(V*h);cm=lo**(d-1)/(V*h)
            def K(a):return cp*(a-np.r_[a[1:],0])+cm*(a-np.r_[0,a[:-1]])
            ka=K(src);k2=K(ka)
            norm=lambda a:float(np.sqrt(np.dot(V,a*a)))
            k15=float(np.sqrt(np.dot(hi**(d-1)/h,(np.r_[ka[1:],0]-ka)**2)))
            rows.append(dict(d=d,n=n,K1=norm(ka),K1p5=k15,K2=norm(k2),K2_origin=float(k2[0])))
    return rows


def weak_window(T,b,H,LapH,Tend,normalization):
    """Displacement-only equivalent of original continuum fixed-window rows.

    T,b,H,LapH are same-clock arrays; H and LapH are axial TT values,
    not bare radial prepotential or legacy radial second derivative.
    Caller supplies positive original window normalization. Quadrature
    is a numerical approximation, not a signed interval certificate.
    """
    T,b,H,LapH=map(lambda x:np.asarray(x,float),(T,b,H,LapH))
    assert T.ndim==1 and T.shape==b.shape==H.shape==LapH.shape
    assert np.all(np.diff(T)>0) and np.all(b>0) and normalization>0
    u=10*(T-Tend+.15);mask=abs(u)<1
    assert T[0]<=Tend-.25 and T[-1]>=Tend-.05
    w=np.zeros_like(T);w1=w.copy();w2=w.copy()
    x=1/(1-u[mask]**2);q=u[mask]
    w[mask]=np.exp(1-x)/normalization
    w1[mask]=-20*q*x*x*w[mask]
    w2[mask]=100*(-2*x*x-8*q*q*x**3+4*q*q*x**4)*w[mask]
    beta=np.sqrt(1+b*b);v=-b/beta;acc=b/(1+b*b)**2
    A=b*b*(1+b*b);Ap=(2*b+4*b**3)*v
    App=(2+12*b*b)*v*v+(2*b+4*b**3)*acc
    out={}
    for name,fac,extra,sign in (('E4',.25,0,-1),('SMS',.5,2,1)):
        B=-b**4/beta+extra*b*b*beta
        Bp=(-4*b**3/beta+b**5/beta**3+extra*(2*b*beta+b**3/beta))*v
        p=fac*(-A*w2+(B-2*Ap)*w1+(Bp-App)*w)
        out[name]=float(np.trapz(p*H+sign*fac*b*b*w*LapH,T))
    return out


if __name__=='__main__':
    print(json.dumps(dict(exact=exact(),source_diagnostics=source_diagnostics(),scope='source-level parity trace and FV origin algebra; diagnostic quadrature, no production or proof kernel'),indent=2))
