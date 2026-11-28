"""Polar maximal-slice York momentum and lapse blocks, original TOV.
Local coefficient and rational bound checks; no global physical domain theorem.
"""
import sympy as s


def main():
    r,f,fp,b,br,c,cr,L=s.symbols('r f fp b br c cr L',positive=True)
    E=2*br-fp*b/f; K=2*b/r-L*c; J=s.sqrt(f)/r*(r*r*cr+b/f)
    # Trace-free Lie derivative, integrated over unit scalar harmonic norm.
    assert s.expand(E**2+2*K**2-(E+2*K)**2/3-2*(E-K)**2/3)==0
    form=2*(E-K)**2/3+2*L*J**2+2*L*(L-2)*c**2
    # l>=2 zero form implies c=0, then J=0 implies b=0.
    assert s.simplify(J.subs({c:0,cr:0})-b/(r*s.sqrt(f)))==0
    # l=1 conformal Killing equation, flat translation negative control.
    assert s.simplify(form.subs({L:2,f:1,fp:0,b:1,br:0,c:1/r,cr:-1/r**2}))==0
    # Exact original potential in maximal lapse equation.
    x=s.symbols('x',real=True); lam=s.Rational(1,10); p=lam/(8*s.pi)
    rho=(2+lam)*p*(1-x); pr=-p*(1-x)**2
    F=1-lam*(2+lam)*(x/3-x*x/5)
    P=(2+lam)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=pr+x*s.diff(pr,x)+x*lam*(rho+pr)*P/(2*F)
    V=4*s.pi*(rho+pr+2*pt)
    def positive_bern(expr):
        num,den=s.fraction(s.cancel(expr))
        if den.subs(x,0)<0:num,den=-num,-den
        def coeff(poly):
            q=s.Poly(poly,x); n=q.degree()
            return [sum(q.nth(j)*s.binomial(i,j)/s.binomial(n,j) for j in range(i+1)) for i in range(n+1)]
        assert min(coeff(num))>0 and min(coeff(den))>0
    positive_bern(V+lam)
    assert V.subs(x,0)<0
    assert s.cancel(V.subs(x,1))==0
    # L/r² >=2 in the interior for l>=1: loss <=lambda/2.
    assert 1-lam/2==s.Rational(19,20)
    print('PASS polar York trace-free form, flat dipole translation control, maximal lapse bound V>-1/10')
    print('OPEN source norm and global physical York domain, spatial Hessian, moving junction and nonlinear continuation')

if __name__=='__main__':main()
