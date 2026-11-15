#!/usr/bin/env python3
"""Exact coupled nonzero Maxwell + varying radion 5D Ricci-flat KK wave.
Coordinates u,v,x,y,w; phi(u)=1+u²; A=b*u dx; kappa=1.
Base ds4²=2du dv + dx² + dy² + H(u,x)du².
H=-(b² phi(u)²/2 + phi''(u)/phi(u))*x².
Computes every 5D Ricci tensor component from the metric.
"""
import sympy as s
u,v,x,y,w,b=s.symbols('u v x y w b', real=True)
coords=(u,v,x,y,w); n=5
phi=1+u**2
potential=b*u
h=-b**2*phi**2/2-s.diff(phi,u,2)/phi
G=s.zeros(n)
G[0,1]=G[1,0]=1
G[0,0]=h*x**2
G[2,2]=1+phi**2*potential**2
G[2,4]=G[4,2]=phi**2*potential
G[3,3]=1
G[4,4]=phi**2
inverse=s.simplify(G.inv())
Gamma=[[[s.factor(sum(inverse[a,l]*(s.diff(G[l,j],coords[i])+s.diff(G[l,i],coords[j])-s.diff(G[i,j],coords[l]))/2 for l in range(n))) for j in range(n)] for i in range(n)] for a in range(n)]
Ric=s.Matrix(n,n,lambda i,j:s.factor(sum(s.diff(Gamma[k][i][j],coords[k])-s.diff(Gamma[k][i][k],coords[j])+sum(Gamma[k][k][l]*Gamma[l][i][j]-Gamma[k][j][l]*Gamma[l][i][k] for l in range(n)) for k in range(n))))
assert Ric==s.zeros(n),Ric
assert s.factor(G.det())==-phi**2
assert s.diff(phi,u)!=0
assert s.diff(potential,u)==b
g=s.zeros(4);g[0,1]=g[1,0]=1;g[0,0]=h*x**2;g[2,2]=g[3,3]=1
F=s.zeros(4);F[0,2]=b;F[2,0]=-b
Fup=g.inv()*F*g.inv()
assert s.simplify(sum(F[i,j]*Fup[i,j] for i in range(4) for j in range(4)))==0
print('PASS: Ricci_5 = 0 (all 25 components); det G5 = -phi²')
print('PASS: phi(u)=1+u² is nonconstant, F_ux=b nonzero, F²=0')
print('PASS: H(u,x)=(-b² phi²/2 - phi_uu/phi) x²')
print('SCOPE: local analytic 5D vacuum fixture; not general KK reduction or quantum gravity')
