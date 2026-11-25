"""Exact polynomial recursion for a source-free moving-wall dual window lift.
The general smooth coefficient remainder is an analytic estimate, not evaluated here.
"""
import json
import sympy as s


def check():
    # Rational clock coordinate u=t+sqrt(1+t²), actual original b,v,beta.
    u,Z,e=s.symbols('u Z e',positive=True);b=2*u/(u*u-1);v=-2*u/(u*u+1);beta=(u*u+1)/(u*u-1);sigma=1/beta**2
    rate=u*(u*u-1)**2/(u*u+1)**2
    clean=lambda p:s.Add(*[s.cancel(c)*Z**i[0] for i,c in s.Poly(s.expand(p),Z).terms()])
    T=lambda p:clean(rate*s.diff(p,u));Dz=lambda p:clean(s.diff(p,Z)-beta*p);Dt=lambda p:clean(T(p)-T(beta)*Z*p)
    D=lambda p:clean(sigma*(s.diff(p,Z,2)-2*beta*s.diff(p,Z)))
    A=lambda p:clean(2*v*Dt(Dz(p))+(T(v)-3/b)*Dz(p))
    B=lambda p:clean(-Dt(Dt(p)))
    assert s.cancel(T(b)-v)==0 and s.cancel(sigma+v*v-1)==0
    def solve(rhs,flux):
        # D maps degree d+1 polynomials onto degree d, constant kernel.
        p=s.S.Zero;remaining=clean(rhs)
        for j in range(s.Poly(remaining,Z).degree(),-1,-1):
            c=s.cancel(s.expand(remaining).coeff(Z,j)/(-2*sigma*beta*(j+1)));q=c*Z**(j+1);p+=q;remaining=clean(remaining-D(q))
        assert remaining==0
        p=clean(p+(sigma*s.diff(p,Z).subs(Z,0)-flux)/(sigma*beta))
        assert clean(D(p)-rhs)==0 and s.cancel(sigma*Dz(p).subs(Z,0)-flux)==0
        return p
    # Nonconstant rational test flux, not a substitute for the original window.
    p=[s.cancel(-u/(sigma*beta))];counts=[]
    for j in range(3):
        rhs=A(p[j])+(B(p[j-1]) if j else 0)
        for l in range(1,j+1):rhs+=-3/b*(-Z/b)**l*Dz(p[j-l])
        p.append(solve(clean(-rhs),-v*T(p[j].subs(Z,0))))
        counts.append(int(s.Poly(p[-1],Z).degree()))
    # Final trace-zero correction; full flux equals test flux identically.
    p.append(clean(-v*T(p[-1].subs(Z,0))*Z/sigma))
    flux=sum(e**j*sigma*Dz(q).subs(Z,0)+e**(j+1)*v*T(q.subs(Z,0)) for j,q in enumerate(p))
    assert s.cancel(flux-u)==0
    # Exact finite Taylor identity for 1/(b+y), valid y>=0, b>0.
    y=s.symbols('y',nonnegative=True)
    for j in range(4):assert s.cancel(1/(b+y)-sum((-y)**l/b**(l+1) for l in range(j+1))-(-y)**(j+1)/(b**(j+1)*(b+y)))==0
    return dict(actual_clock_identities=2,polynomial_orders=3,polynomial_degrees=counts,exact_wall_flux=True,warp_remainders=4,scope='rational test flux, arbitrary-order recursion analytic; no original window coefficient bounds evaluated')

if __name__=='__main__':print(json.dumps(check(),indent=2))
