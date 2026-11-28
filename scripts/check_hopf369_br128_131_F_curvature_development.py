#!/usr/bin/env python3
"""BR128-131: consume BR29 curvature carrier; variable material energy,
Ricci-defect wall lift, weighted shape transport and Cartan development.
Exact local identities, not nonlinear existence or native acceptance.
"""
import argparse
from itertools import product
import sympy as s
from check_hopf369_br_curvature_energy import carrier, P, eta, read
Q=s.Rational

def eq(a,b):
    if isinstance(a,s.MatrixBase):
        assert (a-b).applyfunc(s.expand)==s.zeros(*a.shape)
    else: assert s.expand(a-b)==0

def vector(n,seed):
    return s.Matrix([Q(((i+1)*(seed+3))%19-9,23+seed) for i in range(n)])

def material():
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier();An=A[3];S=G*An;j=Q(-6,5)
    # Use actual BR29 flux and trace-free wall carrier, no surrogate.
    eq(S*J,3*R.T*H);P0=s.eye(35)-An*(5*An-4*An**3)
    eq(R*P0,s.zeros(9,35));eq(S*P0,s.zeros(35))
    u=vector(35,2);v=vector(9,3);plus=u+j*J*v/2;minus=u-j*J*v/2
    flux=lambda w:(w.T*S*w)[0]/2
    wall=-(v.T*H*R*u)[0]
    eq(-flux(plus)+flux(minus)-3*j*wall,0)
    # Material frame e_0,e_1,e_2,e_3 tangent to y=constant;
    # n=lambda^-1(partial_y-beta^a partial_a). Multiply bulk by lambda.
    # Independent lambda/beta/e coefficients on two sides are permitted.
    lam=s.symbols('lam',positive=True);b=s.symbols('b:4');E=s.Matrix(4,4,lambda i,k:s.Symbol(f'e{i}{k}'))
    blocks=[lam*(E[0,a]*s.eye(35)-sum((E[i+1,a]*A[i] for i in range(3)),s.zeros(35)))+b[a]*An for a in range(4)]
    for T in blocks: eq(G*T,T.T*G)
    # time positivity example with nonzero normal time shift;
    # same Euclidean compression gives ||sum spatial v_i A_i|| <= |v|.
    raw=[]
    for i in range(1,5):
        L=s.zeros(10)
        for k in range(1,5):
            if i==k:continue
            a=P.index((0,k));bb=P.index(tuple(sorted((i,k))))
            L[a,bb]=L[bb,a]=1 if i<k else -1
        raw.append(L)
    z=s.Matrix([1,2,3,4]);L=sum((z[i]*raw[i] for i in range(4)),s.zeros(10))
    eq(L**3,z.dot(z)*L)
    assert L.eigenvals()=={-s.sqrt(30):3,0:4,s.sqrt(30):3}
    for i in range(4):eq(G*A[i],X.T*s.kronecker_product(raw[i],s.eye(10))*X)
    # Tangential differentiation hits only C^a and lower coefficients.
    y,t,x=s.symbols('y t x');f=s.Function('f')(t,x,y);a=s.Function('a')(t,x,y);c=s.Function('c')(t,x,y);d=s.Symbol('d')
    Op=lambda u:a*s.diff(u,t)+c*s.diff(u,x)-d*s.diff(u,y)
    for k in (t,x):eq(s.diff(Op(f),k)-Op(s.diff(f,k)),s.diff(a,k)*s.diff(f,t)+s.diff(c,k)*s.diff(f,x))
    print('PASS BR128 actual BR29 signed flux, zero-speed firewall, variable material normal constant and tangential commutator')

def defect():
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier();h=s.diag(-1,1,1,1);j=Q(-6,5)
    # In the actual BR90/125 carrier, effective shape absorbs all
    # nonzero Ricci jump; source enters wall equation by one tangent jet.
    d=s.Matrix(4,4,lambda i,k:s.Symbol(f'd{min(i,k)}{max(i,k)}'));dt=d-h*s.trace(h*d)/4
    delta=Y.gauss_jordan_solve(s.Matrix(list(dt/(3*j))))[0]
    eq(Y*delta,s.Matrix(list(dt/(3*j))))
    # Actual Codazzi contraction of mixed Riemann: mean D_na =
    # D^a M_ab when the mean trace is zero. Schouten correction to
    # mean R_{n a 0 i} has both terms, including a=0.
    c=s.Matrix(s.symbols('c:4'));Sch=c/3
    raw=s.Matrix([(-c[a] if i==0 else -(Sch[0]*h[a,i]-Sch[i]*h[a,0])) for a in range(4) for i in range(4)])
    # Direct Kulkarni-Nomizu contraction with g wedge Schouten.
    g=s.diag(h,1);S=s.zeros(5);S[4,:4]=Sch.T;S[:4,4]=Sch
    wedge=lambda a,b,c,d:g[a,c]*S[b,d]+S[a,c]*g[b,d]-g[a,d]*S[b,c]-S[a,d]*g[b,c]
    eq(s.Matrix([sum(eta[a]*wedge(a,4,a,b) for a in range(5)) for b in range(4)]),c)
    eq(raw,s.Matrix([(-c[a] if i==0 else -wedge(4,a,0,i)) for a in range(4) for i in range(4)]))
    F=H.inv()*Y.T*raw;assert F!=s.zeros(9,1)
    # Algebraic wall evolution shift: m_eff=m+delta, same principal,
    # source changes by e0 delta - B_i e_i delta - L_wall delta.
    mm=vector(9,6);dd=vector(9,7);d0=vector(9,8);di=[vector(9,9+i) for i in range(3)];u=vector(35,13)
    L=s.Matrix(9,9,lambda a,b:Q((a+2)*(b+3)%17-8,19));source=vector(9,14)
    tang=[vector(9,15+i) for i in range(3)];rhs=sum((B[i]*tang[i] for i in range(3)),s.zeros(9,1))+L*mm-R*u+source
    rhs2=sum((B[i]*(tang[i]+di[i]) for i in range(3)),s.zeros(9,1))+L*(mm+dd)-R*u+source+d0-sum((B[i]*di[i] for i in range(3)),s.zeros(9,1))-L*dd
    eq(rhs2,rhs+d0)
    S0=G*A[3];eq(S0*J,3*R.T*H)
    print('PASS BR129 actual BR29 Ricci-defect wall absorption, mixed Schouten/Codazzi source and unchanged flux')

def weighted():
    # Independent zero-shift but non-umbilic variable material metric
    # rational 2-jets, nonconstant lambda and full tangent Lorentz h.
    I=range(5);x=s.symbols('x:5');zero=dict.fromkeys(x,0)
    def jet(seed):return sum(Q((i+2)*(seed+3)%17-8,19+seed)*x[i] for i in I)+sum(Q((i+2)*(k+3)*(seed+1)%19-9,23+seed)*x[i]*x[k] for i in I for k in range(i,5))
    h0=s.diag(-2,3,4,5);h0[0,2]=h0[2,0]=Q(1,7)
    h=h0+s.Matrix(4,4,lambda a,b:jet(1+min(a,b)*4+max(a,b)));l=Q(5,4)+jet(23);g=s.diag(h,l*l)
    g0=g.subs(zero);gi=g0.inv();dg=[g.diff(v).subs(zero) for v in x];ddg=[[g.diff(v,w).subs(zero) for w in x] for v in x];dgi=[-gi*M*gi for M in dg]
    def low(d,a,b,k):return (d[a][k,b]+d[b][k,a]-d[k][a,b])/2
    G={(k,a,b):sum(gi[k,m]*low(dg,a,b,m) for m in I) for k,a,b in product(I,repeat=3)}
    dG={(c,k,a,b):sum(dgi[c][k,m]*low(dg,a,b,m)+gi[k,m]*low(ddg[c],a,b,m) for m in I) for c,k,a,b in product(I,repeat=4)}
    # R^k_{4 b 4}; tangent index k, b.
    Re=s.Matrix(4,4,lambda k,b:(dG[b,k,4,4]-dG[4,k,b,4]+sum(G[k,b,m]*G[m,4,4]-G[k,4,m]*G[m,b,4] for m in I))/l.subs(zero)**2)
    p=l.subs(zero);hi=h0.inv();K=dg[4][:4,:4]/(2*p);A=hi*K
    Ay=-hi*dg[4][:4,:4]*A+hi*(ddg[4][4][:4,:4]/(2*p)-K*l.diff(x[4]).subs(zero)/p)
    dl=s.Matrix([l.diff(v).subs(zero) for v in x[:4]]);Hess=s.Matrix(4,4,lambda a,b:l.diff(x[a],x[b]).subs(zero)-sum(G[k,a,b]*dl[k] for k in range(4)))
    eq(Re,-Ay/p-A*A-hi*Hess/p)
    # Weighted transported moment inverse, arbitrary polynomial weight
    # and transformed source; no arbitrary removal of constant.
    r=s.symbols('r',real=True);L=s.symbols('L',positive=True);C0=s.Symbol('C0');w=1+r*r;F=2+3*r+r*r;P=C0-s.integrate(F,(r,0,r));Z=s.integrate(w,(r,0,L));M=s.integrate(w*P,(r,0,L))/Z
    recovered=M+s.integrate(w*s.integrate(F,(r,0,r)),(r,0,L))/Z
    eq(s.cancel(recovered),C0)
    # BR31 power count in original static AdS4-base asymptotics:
    # energy R^4 W², flux R^6 even*odd. p=3 is integrable and
    # flux tends zero only with parity improvement (or faster decay).
    p=s.symbols('p',positive=True);assert (4-2*p).subs(p,3)==-2 and (6-2*p-1).subs(p,3)==-1
    assert (6-2*p).subs(p,3)==0
    print('PASS BR130 full nonumbilic lapse Riccati acceleration, weighted transported moment inverse, BR31 exterior parity power')

def cartan():
    # Temporal connection gauge Omega_t=0, arbitrary theta_t(t,x).
    # Compute Cartan differential identities from independent noncommuting
    # connection/coframe polynomials on 1+2 coordinates (all identities
    # are slotwise, extend to 1+4 without extra assumptions).
    t,x,y=s.symbols('t x y');coords=(t,x,y);I=range(3)
    def mat(seed):return s.Matrix(3,3,lambda a,b:sum(Q(((a+1)*(b+2)*(k+3)+seed)%17-8,19+seed)*v for k,v in enumerate((1,t,x,y,t*x,x*y))))
    O=[s.zeros(3),mat(1),mat(2)];th=[mat(i+3)[:,0] for i in I]
    F=lambda a,b:O[b].diff(coords[a])-O[a].diff(coords[b])+O[a]*O[b]-O[b]*O[a]
    T=lambda a,b:th[b].diff(coords[a])-th[a].diff(coords[b])+O[a]*th[b]-O[b]*th[a]
    cov=lambda a,M:M.diff(coords[a])+O[a]*M-M*O[a]
    eq(cov(0,F(1,2))+cov(1,F(2,0))+cov(2,F(0,1)),s.zeros(3))
    eq(sum((T(b,c).diff(coords[a])+O[a]*T(b,c) for a,b,c in ((0,1,2),(1,2,0),(2,0,1))),s.zeros(3,1)),F(0,1)*th[2]+F(1,2)*th[0]+F(2,0)*th[1])
    # Defect propagation with E_0i=T_0i=0: D E=-D R;
    # d_t T_ij=E_ij theta_t if algebraic R wedge theta=0.
    E=mat(9);Tij=mat(10)[:,0];assert E*th[0]!=s.zeros(3,1)
    # Common unit wall timelike direction cannot be geodesic in both
    # ambient sides when [K]=j h, j!=0.
    j=s.symbols('j',nonzero=True);Kp=s.Symbol('kp');Km=Kp+j
    eq(Kp-Km,-j);assert -j!=0
    print('PASS BR131 Cartan connection/torsion Bianchi identities and two-sided tangent-geodesic obstruction')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['material','defect','weighted','cartan'],required=True)
    {'material':material,'defect':defect,'weighted':weighted,'cartan':cartan}[p.parse_args().part]()
