"""W3.2 exact bulk radial material Euler acceleration inverse.
Uses the ORIGINAL TOV a,d,V action, not an imposed constitutive source.
Interior d>0 is necessary; at the degenerate wall an independent
Euler trace is required. No Einstein time-evolution existence claim.
"""
import sympy as s


def main():
    Y,r,F,N,Yr,Yt,Yrr,Fr,Ft,Nr,Nt,Ytt=s.symbols(
        "Y r F N Yr Yt Yrr Fr Ft Nr Nt Ytt",real=True)
    a,d,V=[s.Function(t) for t in ("a","d","V")]
    W=d(Y*Y)*(F*Yr**2-Yt**2/N**2)+2*a(Y*Y)*Y**2/r**2+V(Y*Y)
    Dr=lambda z:s.diff(z,Y)*Yr+s.diff(z,Yr)*Yrr+s.diff(z,F)*Fr+s.diff(z,r)
    Dt=lambda z:s.diff(z,Y)*Yt+s.diff(z,Yt)*Ytt+s.diff(z,F)*Ft+s.diff(z,N)*Nt
    E=(s.diff(W,Y)-Dr(s.diff(W,Yr))-Dt(s.diff(W,Yt))
       -(2/r+Nr/N-Fr/(2*F))*s.diff(W,Yr)
       -(Nt/N-Ft/(2*F))*s.diff(W,Yt))
    D=d(Y*Y);A=a(Y*Y);VV=V(Y*Y)
    kinetic=s.diff(E,Ytt)
    assert s.simplify(kinetic-2*D/N**2)==0
    rest=(s.diff(D,Y)*(-F*Yr**2+Yt**2/N**2)
          +2*Y**2*s.diff(A,Y)/r**2+4*A*Y/r**2+s.diff(VV,Y)
          -D*Fr*Yr-2*D*F*Yrr-2*D*F*Yr*(2/r+Nr/N)
          -2*D*Yt*Nt/N**3-D*Yt*Ft/(F*N**2))
    assert s.simplify(E-kinetic*Ytt-rest)==0
    acceleration=-N**2*rest/(2*D)
    assert s.simplify(E.subs(Ytt,acceleration))==0
    # Reopen the exact ORIGINAL material stress/EL background.
    x,l=s.symbols("x lam",positive=True)
    p=l/(8*s.pi);rho=(l+2)*p*(1-x);pr=-p*(1-x)**2
    f=1-l*(l+2)*(x/3-x*x/5)
    P=(l+2)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f)
    aa=(rho+pt)/2;dd=(rho+pr)/(2*f);v0=rho-2*aa-dd*f
    y,z,yp,ff=s.symbols("y z yp ff",real=True)
    Ws=dd.subs(x,y*y)*ff*yp**2+2*aa.subs(x,y*y)*y*y/z**2+v0.subs(x,y*y)
    fb=f.subs(x,r*r);nu=r*l*P.subs(x,r*r)/fb
    B={y:r,z:r,yp:1,ff:fb}
    static=(s.diff(Ws,y).subs(B)
            -s.diff(s.diff(Ws,yp).subs(B),r)
            -(2/r+nu-s.diff(fb,r)/(2*fb))*s.diff(Ws,yp).subs(B))
    assert s.cancel(static)==0
    assert s.factor(dd.subs(x,1))==0
    assert s.factor(s.diff(dd,x).subs(x,1))!=0
    assert s.factor((rho+pr)/(1-x)-(l+2)*p+p*(1-x))==0
    print("PASS exact original-action bulk Euler operator and unique interior acceleration")
    print("PASS static original TOV Euler, kinetic degeneracy and independent wall trace")
    print("OPEN time-integrated Einstein/Euler and moving full GHY/corner")


if __name__=="__main__":
    main()
