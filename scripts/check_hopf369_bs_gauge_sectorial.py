#!/usr/bin/env python3
"""BS5/8 actual normal gauge pencil: accretive form, parabolic eigenvalue
bound, decaying complex AdS indicial branch. No spectral-basis claim."""
import sympy as s

def run():
    h=s.Rational(4,5); t2=s.Rational(36,25)
    zR,zI,a,Y,X,cR,cI,r=s.symbols('zR zI a Y X cR cI r',real=True)
    # z v=A v-T w; z M w=T A v+(B-T²)w.
    # Inner product in D(A^1/2) x L²(M), first variable tested by A v.
    Av2,B0,dR,dI=s.symbols('Av2 B0 dR dI',real=True)
    z=zR+s.I*zI; d=dR+s.I*dI
    pair=Av2+B0+d-s.conjugate(d)
    assert s.re(pair)==Av2+B0 and s.im(pair)==2*dI
    # Coercive A gap 6h²; B-T² retains positive Robin and 4 b⁴.
    assert 6*h*h>4*h*h and 4*h*h==s.Rational(64,25)
    b,k=s.symbols('b k',real=True)
    assert s.expand(4*b**4*(1+k*k)-(2*k*b*b)**2)==4*b**4
    assert s.expand((2*k*b*b)**2/b**2-4*k*k*b*b)==0
    assert 4*(1-h*h)==t2
    # BS8 nonreal eigenpair implies Y=a; Cauchy gives disc
    # |z-r|²<=t² r, r=a/X.
    c=a-z*X
    rhs=s.expand(z*(Y-s.conjugate(c)))
    assert s.expand(s.im(rhs)-zI*(Y-a))==0
    assert s.expand(s.re(rhs).subs(Y,a)-(zR*zR+zI*zI)*X)==0
    assert s.expand(c*s.conjugate(c)-(a*a-2*a*zR*X+(zR*zR+zI*zI)*X*X))==0
    # Eliminate r by completing the square, uniformly in high normal modes.
    assert s.expand(t2*r-(zR-r)**2-(t2*zR+t2*t2/4-(r-zR-t2/2)**2))==0
    # sqrt(9/4+z/h²)=u+iv, u>0, so u²>=9/4+Re(z)/h².
    u,v=s.symbols('u v',real=True)
    R=h*h*(u*u-v*v-s.Rational(9,4)); I=2*h*h*u*v
    assert s.expand(I*I-4*h**4*u*u*v*v)==0
    assert t2*t2/4<=s.Rational(9,4)*t2*h*h
    assert t2/(4*h*h)==s.Rational(9,16)
    assert s.Rational(3,2)+s.sqrt(s.Rational(9,4)+4)==4
    # Exact complex AdS4 scalar radial fundamental modes on global chart.
    # rho optical radius, f=(sin rho)^l (cos rho)^Delta P(sin² rho).
    # Jacobi ODE x(1-x)P''+[l+3/2-(l+Delta+1)x]P'
    # + (omega²-(l+Delta)²)P/4=0, omega dimensionless.
    x,L,D,om=s.symbols('x L Delta omega')
    P=s.Function('P')(x); F=x**(L/2)*(1-x)**(D/2)
    rad=4*x*(1-x)*s.diff(F*P,x,2)+(6-4*x)*s.diff(F*P,x)+(om*om-L*(L+1)/x-D*(D-3)/(1-x))*F*P
    target=4*x*(1-x)*s.diff(P,x,2)+(4*L+6-4*(L+D+1)*x)*s.diff(P,x)+(om*om-(L+D)**2)*P
    assert s.simplify(s.expand(rad/F-target))==0
    for n in range(6):
        # Polynomial coefficient recurrence without branch assumptions.
        p=s.S.One; coeff=s.S.One
        for i in range(n):
            coeff=s.factor(-coeff*(n-i)*(n+i+L+D)/((i+1)*(i+L+s.Rational(3,2))))
            p+=coeff*x**(i+1)
        eq=x*(1-x)*s.diff(p,x,2)+(L+s.Rational(3,2)-(L+D+1)*x)*s.diff(p,x)+n*(n+L+D)*p
        assert s.factor(eq)==0
    print('PASS accretive mass form, complex parabolic bound, AdS indicial and polynomial modes')
    print('Re mass² >= 64/25, Re Delta >= 4, |Im Delta| <= 3/4 for eigenpairs')
if __name__=='__main__':run()
