#!/usr/bin/env python3
"""Nontrivial exact 5D KK vacuum: Brinkmann wave + nonzero null Maxwell field.
Coordinates (u,v,x,y,w), 4D base:
ds4²=2du dv+dx²+dy²-(b²x²/2)du²,
A=b*u dx; phi=kappa=1.
All 25 five-dimensional Ricci components are computed directly.
"""
import sympy as s
u,v,x,y,w,b=s.symbols('u v x y w b', real=True)
coords=(u,v,x,y,w); n=5
G=s.zeros(n)
G[0,1]=G[1,0]=1
G[2,2]=G[3,3]=G[4,4]=1
G[0,0]=-b*b*x*x/2
G[2,4]=G[4,2]=b*u
G[2,2]+=b*b*u*u
Gi=s.simplify(G.inv())
Gamma=[[[s.factor(sum(Gi[a,l]*(s.diff(G[l,j],coords[i])+s.diff(G[l,i],coords[j])-s.diff(G[i,j],coords[l]))/2 for l in range(n))) for j in range(n)] for i in range(n)] for a in range(n)]
Ric=s.Matrix(n,n,lambda i,j:s.factor(sum(s.diff(Gamma[k][i][j],coords[k])-s.diff(Gamma[k][i][k],coords[j])+sum(Gamma[k][k][l]*Gamma[l][i][j]-Gamma[k][j][l]*Gamma[l][i][k] for l in range(n)) for k in range(n))))
assert s.simplify(G.det()+1)==0
assert Ric==s.zeros(5),Ric
# F_ux=b; inverse of Brinkmann 4D base has g^uu=0, so F²=0.
base=G[:4,:4].copy()
base[2,2]-=b*b*u*u
inv=base.inv()
F=s.zeros(4);F[0,2]=b;F[2,0]=-b
Fup=inv*F*inv
F2=s.simplify(sum(F[i,j]*Fup[i,j] for i in range(4) for j in range(4)))
assert F2==0 and F[0,2]==b
assert s.simplify(-s.diff(base[0,0],x,2)/2-b*b/2)==0
print('PASS five-dimensional Ricci tensor identically zero for nonzero null EM wave')
print('PASS F_ux=b, F_{mu nu}F^{mu nu}=0, det(G5)=-1')
print('PASS four-dimensional pp-wave Ric_uu=b²/2 balances KK gauge stress')
print('SCOPE: exact classical local KK vacuum solution; not arbitrary curved-base KK reduction')
