"""W3 exact source-action Euler moving-wall trace and signed slope inverse.
Necessary boundary graph data, not bulk Einstein/York/GHY existence.
"""
import sympy as s

def zero(expr):
    z=s.factor(s.cancel(expr))
    assert z==0,z

def main():
    x,r=s.symbols("x r",positive=True)
    Y,g,u,F,N=s.symbols("Y g u F N",real=True)
    ax,dx,vx=s.symbols("a_x d_x V_x",real=True)
    af=s.Function("a");df=s.Function("d");vf=s.Function("V")
    Yr,Yt,Ytt,Yrt,Fr,Ft,Nt=s.symbols("Yr Yt Ytt Yrt Fr Ft Nt",real=True)
    W=df(Y*Y)*(F*Yr**2-Yt**2/N**2)+2*af(Y*Y)*Y**2/r**2+vf(Y*Y)
    WY=s.diff(W,Y);WYr=s.diff(W,Yr);WYt=s.diff(W,Yt)
    Dr=s.diff(WYr,Y)*Yr+s.diff(WYr,Yr)*s.symbols("Yrr")+s.diff(WYr,Yt)*Yrt+s.diff(WYr,F)*Fr
    Dt=s.diff(WYt,Y)*Yt+s.diff(WYt,Yr)*Yrt+s.diff(WYt,Yt)*Ytt+s.diff(WYt,F)*Ft+s.diff(WYt,N)*Nt
    alpha,beta=s.symbols("alpha beta")
    EL=WY-Dr-Dt-alpha*WYr-beta*WYt
    w=s.expand(EL.subs({Y:1,r:1,Yr:g,Yt:u}))
    for fn,first in ((af,ax),(df,dx),(vf,vx)):
        for item in list(w.atoms(s.Subs)):
            if item.expr.has(fn):w=w.subs(item,first)
        w=w.subs(fn(1),0)
    expected=2*dx*(-F*g*g+u*u/N**2)+4*ax+2*vx
    zero(w-expected)
    f0=s.symbols("f0",positive=True)
    trace=s.factor(w.subs(vx,(2*dx*f0-4*ax)/2))
    zero(trace-2*dx*(f0-F*g*g+u*u/N**2))
    Rdot=s.symbols("Rdot",real=True)
    g2=s.factor(f0/(F-Rdot**2/N**2))
    uwall=-Rdot*g
    zero(trace.subs(u,uwall).subs(g*g,g2))
    g2static=s.factor(g2.subs(F,f0))
    zero(g2static-1-Rdot**2/(N**2*f0-Rdot**2))
    h=s.symbols("h",positive=True)
    profile=r+h*r*(r*r-1)/2
    zero(profile.subs(r,1)-1)
    zero(s.diff(profile,r).subs(r,1)-(1+h))
    zero(profile.subs(r,0))
    hs=s.sqrt(g2static)-1
    zero(s.simplify(s.diff(hs,Rdot).subs(Rdot,0)))
    zero(s.simplify(s.diff(hs,Rdot,2).subs(Rdot,0))-1/(N*N*f0))
    zero((F*g*g-u*u/N**2).subs(u,uwall).subs(g*g,g2)-f0)
    assert s.factor(trace.subs({F:f0,g:1,u:-Rdot}))!=0
    print("PASS exact original-action Euler moving-wall trace and nonlinear slope inverse")
    print("PASS static EL cancellation and O(velocity²) smooth gradient repair")
    print("OPEN full Einstein constraints, bulk material Euler, moving spacetime and GHY")

if __name__=="__main__":main()
