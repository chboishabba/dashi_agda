#!/usr/bin/env python3
"""BR31/BS12: nonlinear normal holonomy graph, weighted AdS curvature parity.
Exact geometry and sufficient reflecting asymptotic class, not global existence.
"""
import sympy as s
from itertools import product,combinations


def graph():
    h=s.diag(-1,1,1,1); d=s.Matrix(s.symbols('d0:4')); K=s.Matrix(4,4,lambda a,b:s.Symbol('k%d%d'%(min(a,b),max(a,b))))
    Hess=s.Matrix(4,4,lambda a,b:s.Symbol('H%d%d'%(min(a,b),max(a,b))))
    F=h+d*d.T; z=1+(d.T*h*d)[0]; inv=h-h*d*d.T*h/z
    assert (F*inv-s.eye(4)).applyfunc(s.cancel)==s.zeros(4)
    # Unnormalized defining-function conormal and four graph tangents.
    g=s.diag(-1,1,1,1,1); v=(-d).col_join(s.ones(1,1)); E=s.eye(4).col_join(d.T)
    assert E.T*v==s.zeros(4,1) and (v.T*g*v)[0]==z and E.T*g*E==F
    # In a normal-parallel Gaussian chart, Hess(F) blocks are K-Hess(ell),
    # K h^-1 d, and 0. The second fundamental form is /sqrt(z).
    a=K*h*d; D=(K-Hess).row_join(a).col_join(a.T.row_join(s.zeros(1)))
    assert E.T*D*E==K-Hess+d*a.T+a*d.T
    # Linear holonomy relation between Gaussian chart and canonical BS11.
    n,L=s.symbols('n L',positive=True); w2=1+n*n;w4=1+n**4
    oldphi=n*n+n-1;oldbeta=2*n+n**3
    I2=s.integrate(w2,(n,0,L));I4=s.integrate(w4,(n,0,L));Q=s.Symbol('Dchi')
    int2=s.integrate(w2,n);int2=int2-int2.subs(n,0)
    xi0=-s.integrate(oldphi,n);xi0=xi0-xi0.subs(n,0)
    # Model a directional derivative of the normal transport xi0 independently.
    dxi0=xi0;dxc=dxi0-2*Q*int2
    A=s.integrate(oldbeta+w2*dxc,(n,0,L))/I4
    U=-s.integrate(oldbeta+w2*dxi0,(n,0,L))
    assert s.factor(U+I4*A+I2**2*Q)==0
    assert s.factor(s.integrate(w2*int2,(n,0,L))-I2**2/2)==0
    print('PASS nonlinear graph metric/extrinsic curvature and linear holonomy transport')


def exterior():
    t,x,y,r=s.symbols('t x y r'); xx=(t,x,y,r); E=s.diag(-1,1,1,1); I=range(4)
    pairs=list(combinations(I,2)); eta=[-1,1,1,1]
    # Arbitrary nontrivial tangential polynomial jets, compactified FG gauge.
    T=s.Matrix(3,3,lambda a,b:(a+b+1)*t*x+(a+1)*(b+1)*x*y+(a+b+2)*t*y+(a+b+3)*y*y)
    for p in (3,4,5):
        u=s.zeros(4);u[:3,:3]=r**p*T
        def R(a,b,c,d):
            return (s.diff(u[a,d],xx[c],xx[b])+s.diff(u[b,c],xx[d],xx[a])-s.diff(u[a,c],xx[d],xx[b])-s.diff(u[b,d],xx[c],xx[a]))/2
        Ric=s.Matrix(4,4,lambda b,d:sum(eta[a]*R(a,b,a,d) for a in I));sc=s.trace(E*Ric)
        W={}
        for a,b in pairs:
            for c,d in pairs:
                v=r*r*(R(a,b,c,d)-(E[a,c]*Ric[b,d]+E[b,d]*Ric[a,c]-E[a,d]*Ric[b,c]-E[b,c]*Ric[a,d])/2+sc*(E[a,c]*E[b,d]-E[a,d]*E[b,c])/6)
                v=s.expand(v);W[a,b,c,d]=v
                power=p+int((a,b,c,d).count(3)%2==1)
                assert v==0 or min(m[0] for m,k in s.Poly(v,r).terms())>=power
        def w(a,b,c,d):
            if a==b or c==d:return 0
            return (1 if a<b else -1)*(1 if c<d else -1)*W[(*sorted((a,b)),*sorted((c,d)))]
        flux=s.expand(sum(w(0,i,a,b)*w(3,i,a,b) for i in (1,2) for a,b in pairs))
        assert flux==0 or min(m[0] for m,k in s.Poly(flux,r).terms())>=2*p+1
    # Reference weighted slice measure N^3 dvol ~ R^4 dR, outer work ~ R^6.
    R0,c,b=s.symbols('R c b',positive=True);N=b*s.sqrt(1+c*R0**2)
    assert s.simplify(N**3*b**3*R0**2/s.sqrt(1+c*R0**2)-b**6*R0**2*(1+c*R0**2))==0
    assert s.simplify(N**4*b**2*R0**2-b**6*R0**2*(1+c*R0**2)**2)==0
    print('PASS compactified Weyl radial parity for p=3,4,5 and exact weighted measures')

if __name__=='__main__':graph();exterior()
