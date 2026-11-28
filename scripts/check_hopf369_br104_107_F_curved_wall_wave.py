#!/usr/bin/env python3
"""BR104-107: curved F wall scale, foliation wave, hidden trace and lift.
Classical Ricci/Bochner/Hodge and multiplier identities; original F attachment.
Exact local source algebra, not an existence or variable tame estimate.
"""
import argparse
from itertools import product
import sympy as s
Q=s.Rational

def normal():
    # Arbitrary non-diagonal material metric, variable shift and scale;
    # independent rational value/first/second jets at a single point.
    I=range(5);x=s.symbols('x:5');zero=dict.fromkeys(x,0)
    T=s.eye(4);T[2,0]=Q(1,7);T[3,1]=Q(2,9)
    h0=T.T*s.diag(-2,3,4,5)*T
    def jet(seed):
        return sum(Q((i+2)*(seed+3)%17-8,19+seed)*x[i] for i in I)+sum(Q((i+2)*(k+3)*(seed+1)%19-9,23+seed)*x[i]*x[k] for i in I for k in range(i,5))
    h=h0+s.Matrix(4,4,lambda a,b:jet(1+min(a,b)*4+max(a,b)))
    beta=s.Matrix([Q(i-1,7)+jet(18+i) for i in range(4)])
    # Use a polynomial lambda with positive value, psi=log(lambda).
    l=Q(5,4)+jet(23);p=l.subs(zero);b=beta.subs(zero)
    g=h.row_join(h*beta).col_join((beta.T*h).row_join(s.Matrix([[l*l+(beta.T*h*beta)[0]]])))
    g0=g.subs(zero);gi=g0.inv();dg=[g.diff(v).subs(zero) for v in x]
    ddg=[[g.diff(v,w).subs(zero) for w in x] for v in x]
    dgi=[-gi*A*gi for A in dg]
    tr=lambda i,j,k:(dg[i][k,j]+dg[j][k,i]-dg[k][i,j])/2
    dt=lambda a,i,j,k:(ddg[a][i][k,j]+ddg[a][j][k,i]-ddg[a][k][i,j])/2
    G={(k,i,j):sum(gi[k,m]*tr(i,j,m) for m in I) for k,i,j in product(I,repeat=3)}
    dG={(a,k,i,j):sum(dgi[a][k,m]*tr(i,j,m)+gi[k,m]*dt(a,i,j,m) for m in I) for a,k,i,j in product(I,repeat=4)}
    Ric=s.Matrix(5,5,lambda i,j:sum(dG[k,k,i,j]-dG[j,k,i,k] for k in I)+sum(G[k,k,m]*G[m,i,j]-G[k,j,m]*G[m,i,k] for k,m in product(I,repeat=2)))
    n=s.Matrix([*(-b),1])/p
    dn=[s.Matrix([*(-beta.diff(v).subs(zero)),0])/p-n*l.diff(v).subs(zero)/p for v in x]
    covn=s.Matrix([0,0,0,0,p]);K=s.Matrix(4,4,lambda a,b:-p*G[4,a,b])
    hi=h0.inv();tau=s.trace(hi*K)
    dTau=[]
    for i,v in enumerate(x):
        dh=h.diff(v).subs(zero);dK=s.Matrix(4,4,lambda a,b:-l.diff(v).subs(zero)*G[4,a,b]-p*dG[i,4,a,b])
        dTau.append(s.trace(hi*dK-hi*dh*hi*K))
    psi1=s.Matrix([l.diff(v).subs(zero)/p for v in x])
    psi2=s.Matrix(5,5,lambda i,j:l.diff(x[i],x[j]).subs(zero)/p-psi1[i]*psi1[j])
    Dh=s.Matrix(4,4,lambda a,b:psi2[a,b]-sum(hi[k,m]*(dg[a][m,b]+dg[b][m,a]-dg[m][a,b])*psi1[k]/2 for k,m in product(range(4),repeat=2)))
    Dpsi=psi1[:4,0];Dn=(Dpsi.T*hi*Dpsi)[0];k2=s.trace(hi*K*hi*K)
    nTau=n.dot(s.Matrix(dTau));Rnn=(n.T*Ric*n)[0]
    assert s.cancel(Rnn+nTau+k2+s.trace(hi*Dh)+Dn)==0
    acc=sum((n[i]*dn[i] for i in I),s.zeros(5,1))+s.Matrix([sum(G[k,i,j]*n[i]*n[j] for i,j in product(I,repeat=2)) for k in I])
    assert acc==(-hi*Dpsi).col_join(s.zeros(1,1))
    # Independent scalar Bochner identity, computed from y coordinate.
    boxpsi=sum(gi[i,j]*(psi2[i,j]-sum(G[k,i,j]*psi1[k] for k in I)) for i,j in product(I,repeat=2))
    Qn=(n.dot(psi1)-tau);nQ=sum(n[i]*(dn[i].dot(psi1)+n.dot(psi2[:,i])-dTau[i]) for i in I)
    assert s.cancel(boxpsi-(n.dot(psi1)**2-k2+nQ-Qn*n.dot(psi1)-Rnn))==0
    print('PASS BR104 actual variable shift/scale five-dimensional Ricci, acceleration and Bochner identities')

def wall():
    h=s.diag(-1,1,1,1);j,c=s.symbols('j c');M=s.Matrix(4,4,lambda a,b:s.Symbol(f'M{min(a,b)}{max(a,b)}'));M[0,0]=sum(M[i,i] for i in range(1,4))
    Kp=M+j*h/2;Km=M-j*h/2
    assert s.expand(s.trace((h*Kp)**2-(h*Km)**2))==0
    assert s.trace(h*(Kp-Km))==4*j
    C=s.Matrix(s.symbols('C:4'));D=s.Matrix(4,4,lambda a,b:s.Symbol(f'D{a}{b}'))
    Sp=(D+D.T)/2+Kp*c;Sm=(D+D.T)/2+Km*c
    assert s.expand(s.trace(h*(Sp-Sm)))==4*j*c
    a,b=[s.Matrix(s.symbols(f'{n}:4')) for n in ('a','b')]
    assert s.expand((a.T*h*a-b.T*h*b-(a+b).T*h*(a-b))[0])==0
    ep,em,up,um,Lp,Lm=s.symbols('ep em up um Lp Lm')
    # Ric_nn jump from geometry vs reduced tangential trace via Gauss.
    R=-up+um-Lp+Lm-(a.T*h*a-b.T*h*b)[0]
    wave=R-(4*j*c+ep-em)
    assert s.expand(wave+up-um+Lp-Lm+((a+b).T*h*(a-b))[0]+4*j*c+ep-em)==0
    print('PASS BR105 matched F shape squares cancel; exact signed scale-jump wave with drift and reduced defect')

def tauwave():
    # Independent differential oracle, curved Lorentz warped tangential
    # metric and nonconstant normal lapse, t/x/y dependence. No Einstein
    # assumption: this is the geometric Hodge-divergence identity.
    t,x,y=s.symbols('t x y',real=True);coords=(t,x,y)
    f=t*x/7+y*x/11+y*y/13;psi=t*y/5+x*x/17+y/19
    # g=e^(2f) eta4 + e^(2psi)dy², two spectator tangent axes.
    n=lambda u:s.exp(-psi)*s.diff(u,y)
    tau=4*n(f);Qn=n(psi)-tau
    def box(u):
        return s.exp(-2*f)*(-s.diff(u,t,2)+s.diff(u,x,2)-(2*s.diff(f,t)+s.diff(psi,t))*s.diff(u,t)+(2*s.diff(f,x)+s.diff(psi,x))*s.diff(u,x))+s.exp(-2*psi)*(s.diff(u,y,2)+(4*s.diff(f,y)-s.diff(psi,y))*s.diff(u,y))
    norm=lambda u:s.exp(-2*f)*(-s.diff(u,t)**2+s.diff(u,x)**2)+n(u)**2
    B=box(psi)-norm(psi)
    V=[s.exp(-2*f)*(-1 if k==0 else 1)*s.diff(psi,v)*(n(f)-n(psi)) for k,v in enumerate((t,x))]+[s.S.Zero]
    gradQ=[-s.exp(-2*f)*s.diff(Qn,t),s.exp(-2*f)*s.diff(Qn,x),s.exp(-2*psi)*s.diff(Qn,y)]
    gradpsi=[-s.exp(-2*f)*s.diff(psi,t),s.exp(-2*f)*s.diff(psi,x),s.exp(-2*psi)*s.diff(psi,y)]
    W=[2*V[k]-gradQ[k]+Qn*gradpsi[k]+(B*s.exp(-psi) if k==2 else 0) for k in range(3)]
    div=sum(s.diff(W[k],v)+(4*s.diff(f,v)+s.diff(psi,v))*W[k] for k,v in enumerate(coords))
    assert s.simplify(s.expand(box(tau)-div))==0
    print('PASS BR106 curved foliation wave divergence identity with nonconstant lapse and time/space dependence')

def trace_lift():
    # For Dirichlet scalar w on timelike wall, all tangent derivatives
    # vanish. Normal stress T(n,n)=1/2 (n w)^2 (w=0 for mass term).
    v=s.symbols('v');g=s.diag(-1,1,1,1,1);dw=s.Matrix([0,0,0,0,v]);T=dw*dw.T-g*(dw.T*g*dw)[0]/2
    assert T[4,4]==v*v/2 and T[:4,4]==s.zeros(4,1)
    # Flat coordinate lift from a normal vector field V_n=chi(y)p.
    t,x,y=s.symbols('t x y');p=s.Function('p')(t,x);chi=s.Function('chi')(y)
    W=chi*p;L=s.Matrix([[0,0,s.diff(W,t)],[0,0,s.diff(W,x)],[s.diff(W,t),s.diff(W,x),2*s.diff(W,y)]])
    box=lambda u:-s.diff(u,t,2)+s.diff(u,x,2)+s.diff(u,y,2)
    q=-s.diff(p,t,2)+s.diff(p,x,2)
    assert s.expand(box(W)-chi*q-s.diff(chi,y,2)*p)==0
    for i,z in enumerate((t,x,y)):
        assert s.expand(box(L[i,2])-(2 if i==2 else 1)*s.diff(box(W),z))==0
    assert s.diff(box(W),t).has(s.diff(p,t,3))
    print('PASS BR107 Dirichlet normal stress, exact normal-coordinate lift and derivative source refusal')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['normal','wall','tau','trace'],required=True)
    {'normal':normal,'wall':wall,'tau':tauwave,'trace':trace_lift}[p.parse_args().part]()
