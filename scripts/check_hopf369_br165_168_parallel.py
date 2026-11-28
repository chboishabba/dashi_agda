#!/usr/bin/env python3
"""BR165-168: original carrier parity, KK spin connection, local symbol, sign region."""
import argparse
from itertools import product
import sympy as s
Q=s.Rational

def eq(a,b):
    if isinstance(a,s.MatrixBase): assert (a-b).applyfunc(s.simplify)==s.zeros(*a.shape)
    else: assert s.simplify(a-b)==0

def donor():
    from check_hopf369_br_curvature_energy import carrier
    from check_hopf369_br143_145_parallel import trace
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier()
    pairs,X2,Q0,M,D,L,E,Sc,T,Tsp,Z=trace()
    eq(X,X2)
    for i in range(4):eq(G*A[i],X.T*M[i]*X)
    eq(G*A[3]*J,3*R.T*H)
    print('PASS BR165 original BR27 carrier equals BR143 embedding and all four compressed symbols; signed work replay')

def gamma():
    I=s.eye(2);z=s.zeros(2);sx=s.Matrix([[0,1],[1,0]]);sy=s.Matrix([[0,-s.I],[s.I,0]]);sz=s.diag(1,-1)
    g=[s.I*s.diag(1,1,-1,-1)]+[z.row_join(a).col_join(a.row_join(z)) for a in (sx,sy,sz)]
    g.append(s.I*g[0]*g[1]*g[2]*g[3]) # square +1
    eta=[-1,1,1,1,1]
    for a,b in product(range(5),repeat=2):eq(g[a]*g[b]+g[b]*g[a],2*eta[a]*s.eye(4) if a==b else s.zeros(4))
    return g,eta

def spin():
    g,eta=gamma();f=s.symbols('f',positive=True);v=s.symbols('v:4',real=True)
    F=s.zeros(4)
    for a in range(4):
        for b in range(a+1,4):F[a,b]=s.Symbol(f'F{a}{b}',real=True);F[b,a]=-F[a,b]
    # O[A,B,C] is lower-index connection Omega_AB(E_C), correction to base.
    O={k:s.S.Zero for k in product(range(5),repeat=3)}
    for a in range(4):
        O[4,a,4]=v[a];O[a,4,4]=-v[a]
        for b in range(4):O[4,a,b]=f*F[a,b]/2;O[a,4,b]=-f*F[a,b]/2;O[a,b,4]=-f*F[a,b]/2
    # dtheta^A(E_B,E_C) from the KK coframe; base correction is zero.
    for a,b,c in product(range(5),repeat=3):
        d=(f*F[b,c] if b<4 and c<4 else v[b] if c==4 and b<4 else -v[c] if b==4 and c<4 else 0) if a==4 else 0
        eq(d+eta[a]*(O[a,c,b]-O[a,b,c]),0)
    term=sum((g[c]*O[a,b,c]*g[a]*g[b]/4 for a,b,c in O),s.zeros(4))
    target=sum((v[a]*g[a]/2 for a in range(4)),s.zeros(4))+f*g[4]*sum((F[a,b]*g[a]*g[b] for a,b in product(range(4),repeat=2)),s.zeros(4))/8
    eq(term,target)
    print('PASS BR166 all KK coframe torsion slots and exact spin connection contraction')

def symbol():
    g,eta=gamma();m,b,x,y,z=s.symbols('m b x y z',real=True);I=s.eye(4)
    Hm=-s.I*m*g[0];Hp=s.I*b*g[0]*g[4]*g[1]*g[2];Hk=-g[0]*(x*g[1]+y*g[2]+z*g[3]);H=Hm+Hp+Hk
    eq(H,H.conjugate().T);eq(Hm*Hp+Hp*Hm,s.zeros(4));eq(Hp**2,b*b*I)
    D=H**2-(m*m+x*x+y*y+z*z+b*b)*I
    eq(D**2,4*b*b*(x*x+y*y)*I);eq(s.trace(D),0)
    E=s.symbols('E');eq(H.charpoly(E).as_expr(),(E*E-m*m-x*x-y*y-z*z-b*b)**2-4*b*b*(x*x+y*y))
    eq(H.subs({x:0,y:0,z:0})**2,(m*m+b*b)*I)
    print('PASS BR167 central frozen Dirac symbol: no linear rest shift, anisotropic transverse dispersion')

def region():
    # Same conservative error ledger as BR161, now bound uniformly on
    # eps in (0,e0] for fixed normalized kappa=K0=1,p0=1/4.
    t=s.symbols('t',positive=True);pi=Q(22,7);q0=(32+2*pi)/4+(32+4*pi/3)/8
    U=24;G=176;L1=2*pi*pi+2*pi*pi/3;gp=U+L1/12
    lo=Q(1113,1000)/20;hi=Q(1114,1000)/20
    eh=3*(7*q0*G+7*U*gp)+Q(7,4)*q0*L1+q0*hi
    # error / eps² grows monotonically with t=eps² in admitted range
    er=t*(2*eh+8*q0*hi+8*q0*64/(1-64*t))
    e0=Q(1,1200);t0=e0*e0
    assert 7*q0*t0<1 and 64*t0<Q(1,2)
    print('BR168 normalized upper coefficient at eps=1/1200:',s.N(-2*lo+er.subs(t,t0),12))
    assert er.subs(t,t0)<2*lo
    print('PASS BR168 uniform nonlinear initial sign for 0<|eps|<=1/1200 at normalized parameters')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['donor','spin','symbol','region'],required=True)
    {'donor':donor,'spin':spin,'symbol':symbol,'region':region}[p.parse_args().part]()
