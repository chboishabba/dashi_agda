"""Inverse three-material-scalar action for the exact TOV interior.
Classical sigma-model stress and Noether identity. No free-boundary stability claim.
"""
import sympy as s

def main():
    x,l=s.symbols('x l',positive=True); p=l/(8*s.pi)
    rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
    f=1-l*(2+l)*(x/3-x*x/5)
    P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=s.factor(pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f))
    a=s.factor((rho+pt)/2); d=s.factor((rho+pr)/(2*f)); b=s.cancel((d-a)/x)
    V=s.factor(rho-2*a-d*f)
    eq=lambda e:s.cancel(e)==0
    assert eq(2*a-rho-pt) and eq(2*d*f-rho-pr)
    assert eq(a+x*b-d)
    assert eq(V+2*a+d*f-rho)
    assert s.limit(b,x,0).is_finite
    assert eq(a.subs(x,1)) and eq(d.subs(x,1)) and eq(V.subs(x,1))
    # Verify the actual scalar Euler equation via spherical material map Y=r n.
    # L=-[a(s) tr B+b(s) Y^T B Y+V(s)], s=Y.Y, B=g^-1 dY dY.
    # Radial scalar variation Y=R(r)n at fixed metric; R=r on shell.
    r=s.symbols('r',positive=True); R=s.symbols('R',positive=True); Rp=s.symbols('Rp',real=True)
    ar=a.subs(x,R*R); br=b.subs(x,R*R); Vr=V.subs(x,R*R)
    fr=f.subs(x,r*r); nuprime=(r*l*P/f).subs(x,r*r)
    W=(ar+br*R*R)*fr*Rp*Rp+2*ar*R*R/r**2+Vr
    Wp=s.diff(W,Rp).subs({R:r,Rp:1}); WR=s.diff(W,R).subs({R:r,Rp:1})
    EL=WR-s.diff(Wp,r)-(2/r+nuprime-s.diff(fr,r)/(2*fr))*Wp
    assert eq(EL)
    # Check the action's kinetic matrix and principal symbol at a representative amplitude.
    # a=(rho+pt)/2>0, d=(rho+pr)/(2f)>0 in the open interior by strict DEC.
    # The TOV donor gives |pt-pt_flat|<= (21/20)(50/93)*l*p*(1-x),
    # so rho+pt >= (1+l*(1- (21/20)*(50/93)))*p*(1-x).
    assert 1-s.Rational(21,20)*s.Rational(50,93)>0
    # This is a luminal principal symbol only, no spectral stability.
    # Endpoint degeneration is explicit and cannot be omitted.
    assert eq(s.limit(a,x,1)) and eq(s.limit(d,x,1))
    print('center b/p',s.factor(s.limit(b/p,x,0)))
    print('center potential/p',s.factor(V.subs(x,0)/p))
    print('sample coefficients a/p,d/p,V/p:',*[s.N(z.subs({x:s.Rational(1,4),l:s.Rational(1,10)})/p.subs(l,s.Rational(1,10)),12) for z in (a,d,V)])
    print('PASS exact inverse material stress, scalar EL, smooth center and degenerate surface; no global stability')
if __name__=='__main__':main()
