#!/usr/bin/env python3
"""Exact nonlinear polarisation, Hall/Pedersen, line and two-world work.
These are specified material laws, not extracted Smith/Filsinger constants.
"""
import sympy as S
def nonlinear_material():
 t=S.symbols('t',real=True)
 v,p,c,eta,beta,eps=[S.Function(k)(t) for k in ('V','P','chi','eta','beta','eps')]
 U=eps*v*v/2+p*p/(2*c)+beta*p**4/4
 dp=(v-p/c-beta*p**3)/eta
 dU=S.diff(U,t)
 w=v*(eps*S.diff(v,t)+S.diff(p,t))-eta*S.diff(p,t)**2-p*p*S.diff(c,t)/(2*c*c)
 assert S.simplify((dU-w).subs(S.diff(p,t),dp).subs({S.diff(eps,t):0,S.diff(beta,t):0}))==0
def hall_pedersen():
 x,y,z,p,h,l=S.symbols('Ex Ey Ez P H parallel',real=True)
 Jx=p*x+h*y;Jy=p*y-h*x;Jz=l*z
 assert S.expand(x*Jx+y*Jy+z*Jz-p*(x*x+y*y)-l*z*z)==0
def telegrapher(N=5):
 C,L,R,G,rl,Is,Id=S.symbols('C L R G Rload Is Id',real=True)
 v=S.symbols('v:'+str(N));i=S.symbols('i:'+str(N-1));dp=S.symbols('dp:'+str(N))
 eta=S.symbols('eta')
 dv=[];di=[(v[j]-v[j+1]-R*i[j])/L for j in range(N-1)]
 for j in range(N):
  inflow=Is if j==0 else i[j-1]
  outflow=v[j]/rl if j==N-1 else i[j]
  if j==N//2:inflow+=Id
  dv.append((inflow-outflow-G*v[j]-dp[j])/C)
 rate=sum(C*v[j]*dv[j]+(v[j]-eta*dp[j])*dp[j] for j in range(N))
 rate+=sum(L*i[j]*di[j] for j in range(N-1))
 losses=G*sum(q*q for q in v)+R*sum(q*q for q in i)+eta*sum(q*q for q in dp)
 assert S.simplify(rate-(v[0]*Is+v[N//2]*Id-v[-1]**2/rl-losses))==0
def two_worlds():
 l1,l0,d1,d0,c1,c0,n1,n0,e1,e0,f1,f0,h1,h0=S.symbols('L1 L0 D1 D0 C1 C0 N1 N0 E1 E0 F1 F0 H1 H0')
 b1=d1+c1+n1+e1-l1-h1-f1
 b0=d0+c0+n0+e0-l0-h0-f0
 delta=(l1-l0)-(d1-d0)-(c1-c0)-(n1-n0)-(e1-e0)+(f1-f0)+(h1-h0)
 assert S.expand(delta-(b0-b1))==0
if __name__=='__main__':
 for fn in (nonlinear_material,hall_pedersen,telegrapher,two_worlds):
  fn();print('PASS',fn.__name__)
