"""F8 physical-normal conjugation, moving-wall jump and derivative-free Volterra.
Exact algebra and local rational kernel bounds; no full boundary solve.
"""
from fractions import Fraction as Q
from math import factorial
import json
import sympy as S
from check_f8_local_dual_weld import I
from check_f8_combined_residual import clock_F


def kernel(eta,n=24):
    # R=2F1(-3/2,5/2;1;eta) in direct diamond not touching z=0.
    assert 0<=eta.l<=eta.h<1 and n>=2
    c=Q(1);r=I(1);d=I(0)
    for j in range(1,n+1):
        c*=Q(2*j-5,2)*Q(2*j+3,2)/(j*j)
        r+=c*eta**j;d+=j*c*eta**(j-1)
    c*=Q(2*n-3,2)*Q(2*n+5,2)/(n+1)**2
    # all omitted coefficients positive; value and derivative term ratios <= eta.h
    return r+I(0,c*eta.h**(n+1)/(1-eta.h)),d+I(0,(n+1)*c*eta.h**n/(1-eta.h))


def massive(eta,delta,n=24,m=16):
    # delta=k² (t²-(z-xi)²)/4. Exact mass-shift double series.
    # c_n eta^n (-delta)^l n!/[l!(n+l)!].
    assert 0<=eta.l<=eta.h<1 and delta.l>=0
    c=Q(1);cs=[c]
    for j in range(1,n+2):
        c*=Q(2*j-5,2)*Q(2*j+3,2)/(j*j);cs.append(c)
    R=I();absn=sum(abs(cs[j])*eta.h**j for j in range(n+1));ntail=cs[-1]*eta.h**(n+1)/(1-eta.h)
    for j in range(n+1):
        r=I()
        for l in range(m,-1,-1):r=r*(-delta)+Q(factorial(j),factorial(l)*factorial(j+l))
        R+=cs[j]*eta**j*r
    rho=delta.h/(m+2)**2;assert rho<1
    ltail=delta.h**(m+1)/factorial(m+1)**2/(1-rho)
    abs_l=sum(delta.h**l/factorial(l)**2 for l in range(m+1))
    tail=ntail*(abs_l+ltail)+absn*ltail
    return (R+I(-tail,tail))/2

def pair(b0,b1):
    # Reverse clock from smaller to larger b, exact physical elapsed interval.
    l0,h0=clock_F(b0);l1,h1=clock_F(b1);t=I(l0-h1,h0-l1)
    eta=(t*t-(b1-b0)**2)/(4*b0*b1)
    row=dict(b0=str(b0),b1=str(b1),elapsed=t.floats(),eta=eta.floats())
    if eta.h<1 and eta.l>=0:
        r,d=kernel(eta);row.update(K0=(r/2).floats(),K_t=(d*t/(4*b0*b1)).floats(),K_xi=(d*(b1*b1-b0*b0-t*t)/(8*b1*b0*b0)).floats())
        row["K_modes"]=[massive(eta,I(Q(j)*Q(333,106)/Q("3.012"),Q(j)*Q(355,113)/Q("3.012"))**2*b0*b1*eta).floats() for j in (1,2)]
    return row


def picard_terms(M,A,B,tol=Q(1,10**12)):
    # |R_n| <= x^n/(n!)²; ratio of omitted terms decreases.
    x=Q(M)*Q(A)*Q(B)/4;n=0;term=Q(1)
    while True:
        nxt=term*x/(n+1)**2;rho=x/(n+2)**2
        if rho<1 and nxt/(1-rho)<=tol:return n,nxt/(1-rho)
        term=nxt;n+=1


def check():
    t,z,xi,k=S.symbols('t z xi k',positive=True);P=S.Function('P')(t,z);checks=[]
    def eq(name,l,r):
        assert S.simplify(S.expand(l-r))==0,name;checks.append(name)
    Y=z**S.Rational(3,2)*P
    eq('weighted normal conjugation',(-S.diff(Y,t,2)+S.diff(Y,z,2)-3/z*S.diff(Y,z)-k*k*Y)/z**S.Rational(3,2),-S.diff(P,t,2)+S.diff(P,z,2)-(k*k+S.Rational(15,4)/z**2)*P)
    eq('weighted isometry',z**-3*(z**S.Rational(3,2)*P)**2,P**2)
    # Bessel ODE, conjugated eigenfunction (explicit derivative recurrence).
    p=S.symbols('p',positive=True);f=S.sqrt(z)*S.besselj(2,p*z)
    eq('normal Bessel eigenfunction',-S.diff(f,z,2)+S.Rational(15,4)*f/z**2,p*p*f)
    for f in (S.Integer(1),z**4):eq('zero-frequency static sector',S.diff(f,z,2)-3/z*S.diff(f,z),0)
    eta=(t*t-(z-xi)**2)/(4*z*xi)
    eq('Riemann principal coefficient',S.diff(eta,t)**2-S.diff(eta,z)**2,eta*(1-eta)/z**2)
    eq('Riemann first coefficient',S.diff(eta,t,2)-S.diff(eta,z,2),(1-2*eta)/z**2)
    # delta and delta-prime coefficients after zero extension at moving wall.
    u,a,F,Fp,h,Pz,Pt=S.symbols('u a F Fp h Pz Pt',real=True);den=1+u*u;s=1-u*u;d=u*(3+u*u)/den;e=s/den
    eq('wall trace inverse',(Pz-u*Pt).subs({Pt:(Fp-u*h)/den,Pz:(h+u*Fp)/den}),h)
    eq('wall tangent inverse',(Pt+u*Pz).subs({Pt:(Fp-u*h)/den,Pz:(h+u*Fp)/den}),Fp)
    eq('single layer density',(-a*F-2*u*Pt-(1+u*u)*Pz).subs({Pt:(Fp-u*h)/den,Pz:(h+u*Fp)/den}),-a*F-d*Fp-e*h)
    eq('double layer wavefront jump',s/(2*(1-u)),(1+u)/2)
    eq('diagonal after time integration',1-(1+u)/2+d/2,(1+u)**2/(2*den))
    eq('signed history derivative coefficient',S.diff(d,u)*a-a,2*a*s/den**2)
    eq('signed normal derivative coefficient',d*u+s,(1+3*u*u)/den)
    eq('free outgoing constant velocity trace',-e/2*(-(1+u)/(1-u)),(1+u)**2/(2*den))
    # Accelerated wall, exact outgoing free polynomial, variable coefficient Volterra identity.
    T,r=S.symbols('T r',real=True);bb=1+r/4+r*r/20;uu=S.diff(bb,r);aa=S.diff(uu,r);ff=(r-bb+1)**3
    hh=-(1+uu)*3*(r-bb+1)**2;dd=uu*(3+uu*uu)/(1+uu*uu);ee=(1-uu*uu)/(1+uu*uu);cc=(1+uu)**2/(2*(1+uu*uu))
    eq('accelerating free wall Volterra derivative',S.diff(cc*ff,r),((S.diff(dd,r)-aa)*ff-ee*hh)/2)
    eq('accelerating free wall initial trace',(cc*ff).subs(r,0),0)
    # Memory shear is an exact triangular inverse, with no F' in transported ODEs.
    C0,C1,C0p,C1p,J0,J1,M0,M1,A0,A1,A2,b=S.symbols('C0 C1 C0p C1p J0 J1 M0 M1 A0 A1 A2 b',real=True);K0,K1=S.symbols('K0 K1')
    eq('memory shear round trip',(M0-C0*F)+C0*F,M0)
    eq('memory shear round trip 1',(M1-C1*F)+C1*F,M1)
    for j,C,Cp in ((K0,C0,C0p),(K1,C1,C1p)):eq('derivative-free memory',(j-C*Fp)+Cp*F+C*Fp,j+Cp*F)
    # Source contraction integration by parts with the same original sign.
    w,g,V=S.symbols('w g V',cls=S.Function);F0=S.Function('F')(t);u0=S.Function('u')(t);h0=S.Function('h')(t);J=S.Function('J')(t)
    C=V(t)*S.diff(w(t)*g(t),t)/(1+u0**2)
    expr=-C*S.diff(F0,t)+C*u0*h0+u0*g(t)*J
    eq('source contraction derivative transfer',expr,S.diff(C,t)*F0+C*u0*h0+u0*g(t)*J-S.diff(C*F0,t))
    pairs=[pair(a,b) for a,b in [(Q(1,12),Q(1,11)),(Q(1,10),Q(1,9)),(Q(1,4),Q(3,10)),(Q(1,2),Q(3,5)),(Q(1,12),Q(1))]]
    import mpmath as mp
    mp.mp.dps=60
    for row in pairs:
        if 'K0' not in row:continue
        a,b=map(Q,(row['b0'],row['b1']));a=mp.mpf(a.numerator)/a.denominator;b=mp.mpf(b.numerator)/b.denominator
        clock=lambda x:mp.asinh(1/x)-mp.sqrt(1+x*x)
        T=clock(a)-clock(b);e=(T*T-(b-a)**2)/(4*a*b);R=mp.hyp2f1(-mp.mpf('1.5'),mp.mpf('2.5'),1,e)/2
        # diagnostic against independently evaluated special function (float displays padded).
        lo,hi=row['K0'];assert lo-1e-15<=R<=hi+1e-15;checks.append('local hypergeometric regression')
        for j,(lo,hi) in enumerate(row['K_modes'],1):
            kk=j*mp.pi/mp.mpf('3.012');delta=kk*kk*a*b*e
            f=lambda x:mp.hyp2f1(-mp.mpf('1.5'),mp.mpf('2.5'),1,e*(1-x))*mp.hyp0f1(2,-delta*x)
            val=R-delta/2*mp.quad(f,[0,1]);assert lo<=val<=hi;checks.append('massive local transmutation regression')
    n,tail=picard_terms(Q(15,4)*13**2+Q(3)**2,Q(4),Q(4))
    return dict(checks=len(checks),names=checks,local_pairs=pairs,picard_global_coarse_terms=n,picard_tail=float(tail),scope='exact algebra and local rational normal kernel; global extended potential Picard bound only; no actual Volterra trajectory')

if __name__=='__main__':print(json.dumps(check(),indent=2))
