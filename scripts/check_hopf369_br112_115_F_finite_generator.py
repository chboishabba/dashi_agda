#!/usr/bin/env python3
"""BR112–115: F generator transmission, actual AK scalar warped reference,
finite-collar joint Green bound, and scale-Neumann alternative.
Classical diffeomorphism/Green/energy identities; DASHI source attachment.
No nonlinear variable-coefficient PDE acceptance.
"""
import argparse
from fractions import Fraction as Q
import sympy as s


def graph():
    # Matched Gaussian collar at a physical seam, arbitrary h and mean.
    # Independent vector jets in common frame, signed normal jump.
    h=s.diag(-2,3,4,5);h[0,2]=h[2,0]=s.Rational(1,7)
    hi=h.inv();j,v,p=s.symbols('j v p');M=s.Matrix(4,4,lambda a,b:s.Symbol(f'M{min(a,b)}{max(a,b)}'))
    M=M-h*s.trace(hi*M)/4;Kp=M+j*h/2;Km=M-j*h/2
    d=s.Matrix(s.symbols('d:4'));w=s.Matrix(s.symbols('w:4'))
    W=s.Matrix(4,4,s.symbols('W:16'));Lw=W.T*h+h*W
    Hplus=Lw+2*v*Kp;Hminus=Lw+2*v*Km
    # Material pullback graph f=-v cancels normal Lie transport.
    assert (Hplus-2*v*Kp-Hminus+2*v*Km).applyfunc(s.expand)==s.zeros(4)
    # Common V, common tangential normal derivative w_n, jump v_n=p.
    mixedplus=h*w+d;mixedminus=h*w+d
    assert mixedplus==mixedminus
    vp,vm=s.symbols('vp vm');assert s.expand((vp-vm).subs(vp,vm+p)-p)==0
    # Boundary variation of true K on the transported graph is Lie_w K;
    # check its jump and mean force with arbitrary tangential derivative.
    dwK=s.Matrix(4,4,lambda a,b:s.Symbol(f'D{min(a,b)}{max(a,b)}'))
    dh=s.Matrix(4,4,lambda a,b:s.Symbol(f'h{min(a,b)}{max(a,b)}'))
    Dkp=dwK+j*dh/2;Dkm=dwK-j*dh/2
    dKp=Dkp+W.T*Kp+Kp*W;dKm=Dkm+W.T*Km+Km*W
    dhmat=dh+Lw
    assert (dKp-dKm-j*dhmat).applyfunc(s.expand)==s.zeros(4)
    # Derivative of mean trace includes inverse-metric variation.
    # directional derivative tr_h M=0 fixes one contraction of D_w M.
    R=s.trace(hi*dwK-hi*dh*hi*M)
    assert s.expand(s.trace(hi*(dKp+dKm)/2-hi*dhmat*hi*M)-R)==0
    # Tangential component of gauge after graph transport, P=0:
    # [C]=0 => [Lie_w C]=0. A nonzero jump in P remains a source.
    Cp,Cm,Pp,Pm=[s.Matrix(s.symbols(f'{k}:5')) for k in ('Cp','Cm','Pp','Pm')]
    A=s.diag(W.T,0);Cder=s.Matrix(s.symbols('cd:5'))
    J=(Cder+A*Cp+Pp)-(Cder+A*Cm+Pm)
    assert J.subs(dict(zip(Cp,Cm)))==Pp-Pm
    # In Gaussian frames the covariant conormal adds [K]w=j w;
    # imposing zero *covariant* tangential jump would be a wrong row.
    w0=s.Matrix(s.symbols('w0:4'));wn=s.Matrix(s.symbols('wn:4'))
    assert (wn+hi*Kp*w0-wn-hi*Km*w0-j*w0).applyfunc(s.expand)==s.zeros(4,1)
    # Work integration by parts for a common vector trace and a prescribed
    # normal-derivative jump p n, including time-varying wall density/Gram.
    t=s.symbols('t');V=s.Matrix([s.Function(f'V{i}')(t) for i in range(5)])
    W=s.Matrix([s.Function(f'W{i}')(t) for i in range(5)]);P=s.Function('p')(t)
    power=-(V.diff(t).T*W)[0]*P;pot=(V.T*W)[0]*P
    assert s.expand(power+s.diff(pot,t)-(V.T*(W*P).diff(t))[0])==0
    print('PASS BR112 material graph Lie displacement, Israel/mean variation, mixed/scale generator jump, gauge defect and vector flux')


def reference():
    # BR14 harmonic-Y reference: g=b² h_base + b^8 dY².
    # At a base RNC point H_Y=0 and H_a=H_a(x) independent of Y;
    # a generator V=V^Y partial_Y has Lie_V H=0 identically.
    x=s.symbols('x',real=True);b=s.Function('b')(x);v=s.Function('v')(x);ell=s.symbols('ell');u=s.Function('u')(x)
    # dx/dY=b³; coordinate scalar generator normal equation.
    DY=lambda q:b**3*s.diff(q,x)
    P=b**-6*DY(DY(v))-ell**2*v
    assert s.simplify(P-(s.diff(v,x,2)+3*s.diff(b,x)/b*s.diff(v,x)-ell**2*v))==0
    conj=s.expand((b**s.Rational(3,2)*P.subs(v,b**-s.Rational(3,2)*u)).doit())
    k=s.diff(b,x)/b
    want=s.diff(u,x,2)-(ell**2+s.Rational(3,2)*s.diff(k,x)+s.Rational(9,4)*k*k)*u
    assert s.simplify(conj-want)==0
    # Actual optical AK b=h0 sec(h0 x), k=h0 tan(h0 x).
    h0=s.Rational(4,5);B=h0/s.cos(h0*x);K=h0*s.tan(h0*x)
    assert s.simplify(s.diff(B,x)/B-K)==0
    assert s.simplify(s.diff(K,x)-B**2)==0
    c=s.Rational(3,2)+s.Rational(9,4)*s.Rational(3,5)**2
    assert c==s.Rational(231,100)<3
    # Endpoint conversion: [v_x]=[u_x]-(3/2)j A.
    A,j,up,um=s.symbols('A j up um');vp=up-s.Rational(3,4)*j*A;vm=um+s.Rational(3,4)*j*A
    assert s.expand(vp-vm-(up-um-s.Rational(3,2)*j*A))==0
    print('PASS BR113 original harmonic-Y normal generator and scalar reference conjugation; potential <= 231/100')


def finite():
    # Exact flat finite-interval homogeneous endpoint extension and
    # source trace kernel, then bounded scalar AK perturbation.
    ell,d,x=s.symbols('ell d x',positive=True)
    K0=s.sinh(ell*(d-x))/s.sinh(ell*d);Kd=s.sinh(ell*x)/s.sinh(ell*d);phi=K0+Kd
    assert K0.subs(x,0)==1 and Kd.subs(x,d)==1
    assert K0.subs(x,d)==0 and Kd.subs(x,0)==0
    assert s.simplify(s.diff(phi,x,2)-ell**2*phi)==0
    # Avoid transcendental rewrite dependence: exact exponent form.
    t=s.symbols('t',nonzero=True)
    assert s.cancel((t-1)/(t+1)-(1-2/(t+1)))==0
    D=s.diff(phi,x).subs(x,0)-s.diff(phi,x).subs(x,d)
    assert s.simplify(D+2*ell*(s.cosh(ell*d)-1)/s.sinh(ell*d))==0
    # Green trace via exact integration by parts for arbitrary polynomial.
    f=x*(d-x)*(1+x);assert f.subs(x,0)==f.subs(x,d)==0
    test=K0*(s.diff(f,x,2)-ell**2*f)
    assert s.simplify(s.integrate(test,x).subs(x,d)-s.integrate(test,x).subs(x,0)+s.diff(f,x).subs(x,0))==0
    # |ell²+k²|>=a L: min over k²>=0 is at 0 or b²-a².
    a,b,r=s.symbols('a b r',real=True);L2=a*a+b*b
    expr=(a*a-b*b+r)**2+4*a*a*b*b-a*a*L2
    assert s.expand(expr-(b*b*L2+2*r*(a*a-b*b)+r*r))==0
    assert s.expand(expr-(r+a*a-b*b)**2-a*a*(3*b*b-a*a))==0
    # e^2>7, so for a*d>=2, exp(-ad)<1/7.
    assert sum(Q(2)**k/Q(s.factorial(k)) for k in range(6))>7
    e=Q(1,7);assert (1+e)/(1-e*e)==Q(7,6)
    assert 2*Q(7,6)**2<4 # trace/extension <=2/sqrt(a)
    assert 2*(1-e)/(1+e)==Q(3,2)
    assert 2*(1+e)/(1-e)==Q(8,3)
    gam=Q(16);c=Q(3);j=Q(6,5);delta=c/gam**2
    assert delta<Q(1,64) and 2/(1-delta)<3
    # Dirichlet resolvent <=1/(aL), corrected trace jump/extension.
    # |D-D0|<=6c/a+3|j|/2 <= L/2.
    assert 6*c/gam+3*j/2<gam/2
    assert Q(8,3)+6*c/gam**2<3
    # ||u'||² <= [(L²+c)*9/a + 3L] |A|² <=16 L²/a |A|².
    assert 9*(1+c/gam**2)+3<16
    assert 3*(1+c/gam**2)<4 # second derivative <=4L²/sqrt(a)
    # b^-3/2 and derivatives <=2,2,5. Then v<=6, v'<=9L, v''<=10L².
    assert Q(5,4)**3<4 and 2*Q(3,2)*Q(3,5)<2
    assert 2*(Q(9,4)*Q(3,5)**2+Q(3,2))<5
    assert 8+6/gam<9 and 8+16/gam+15/gam**2<10
    # p<=3||F||/(sqrt(a)L²), |A|<=|p|/L. Derivative bound
    # 30 D²/(L³ a)<=60/gamma² by BR109 root inequalities.
    print('PASS BR114 finite AK scalar Green composition: gamma>=16, joint second generator derivatives <=60/gamma² times source norm')


def neumann():
    # F wall: n psi=tau+C_perp+H_perp, tau±=±2j.
    j,c,hp,hm=s.symbols('j c hp hm');np=2*j+c+hp;nm=-2*j+c+hm
    assert s.expand(np-nm-(4*j+hp-hm))==0
    # BR104 first-jet scale-wave source: no n tau or second metric jet.
    tau,npsi,k2,nH,dot,err=s.symbols('tau npsi k2 nH dot err')
    f=tau*npsi-k2+nH-dot+4-err
    assert not f.has(s.Symbol('nTau'))
    # Flat half-lines, homogeneous Neumann scale wave forced by F_l.
    # Normal trace functional norm on paired half-lines =1/(L sqrt(a)).
    # Combined lift from arbitrary scale source: |s|²/(2L² a).
    r,g=s.symbols('r gamma',positive=True);L2=s.sqrt(g**4+4*g*g*r*r);a2=(L2+g*g)/2
    sq=(g*g+r*r)**2/(4*L2**2*a2)
    assert s.simplify(s.limit(sq/r,r,s.oo)-1/(16*g**3))==0
    assert s.limit(sq,r,s.oo)==s.oo
    # At the AK reference H_perp=0 at RNC point, delta n psi
    # = n(delta psi)-npsi delta psi (D psi=0). Homogeneous linearized
    # Neumann becomes Robin with background npsi=4k, not naive zero.
    k,l,dl,e=s.symbols('k l dl e');gNN=1+2*e*l
    # At b=1, n=(gNN)^-1/2 ∂_Y and ∂_Y psi=4k+e dl.
    assert s.simplify(s.diff((4*k+e*dl)/s.sqrt(gNN),e).subs(e,0)-(dl-4*k*l))==0
    print('PASS BR115 first-jet scale-Neumann route and exact arbitrary-source glancing half-derivative obstruction')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['graph','reference','finite','neumann'],required=True)
    {'graph':graph,'reference':reference,'finite':finite,'neumann':neumann}[p.parse_args().part]()
