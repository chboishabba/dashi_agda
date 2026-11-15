#!/usr/bin/env python3
"""Exact functional family: Ricci-flat five-dimensional circle KK pp-waves.
For arbitrary smooth nonzero phi(u) and a(u), g4=2du dv+dx²+dy²+Hdu²,
A=a(u)dx, and H=-[phi''/phi + phi²(a')²/2] x²,
direct computation produces Ricci5=0 (all 25 components).
Local result only, no general 4D curved-base dimensional reduction.
"""
import sympy as s
u,v,x,y,w=s.symbols("u v x y w", real=True)
phi=s.Function("phi")(u);a=s.Function("a")(u)
h=-s.diff(phi,u,2)/phi-phi**2*s.diff(a,u)**2/2
coords=(u,v,x,y,w);n=5
G=s.zeros(n)
G[0,1]=G[1,0]=1;G[0,0]=h*x**2
G[2,2]=1+phi**2*a**2;G[2,4]=G[4,2]=phi**2*a
G[3,3]=1;G[4,4]=phi**2
Gi=s.simplify(G.inv())
Gamma=[[[s.factor(sum(Gi[t,l]*(s.diff(G[l,j],coords[i])+s.diff(G[l,i],coords[j])-s.diff(G[i,j],coords[l]))/2 for l in range(n))) for j in range(n)] for i in range(n)] for t in range(n)]
Ric=s.Matrix(n,n,lambda i,j:s.factor(sum(s.diff(Gamma[k][i][j],coords[k])-s.diff(Gamma[k][i][k],coords[j])+sum(Gamma[k][k][l]*Gamma[l][i][j]-Gamma[k][j][l]*Gamma[l][i][k] for l in range(n)) for k in range(n))))
assert Ric==s.zeros(5), Ric
assert s.factor(G.det())==-phi**2
base=s.zeros(4);base[0,1]=base[1,0]=1;base[0,0]=h*x**2;base[2,2]=base[3,3]=1
F=s.zeros(4);F[0,2]=s.diff(a,u);F[2,0]=-s.diff(a,u)
Fup=base.inv()*F*base.inv()
assert s.simplify(sum(F[i,j]*Fup[i,j] for i in range(4) for j in range(4)))==0
print("PASS generic smooth phi(u), a(u): all 25 Ricci5 entries vanish")
print("PASS det G5=-phi(u)^2 and F_mu_nu F^mu_nu=0")
print("CONDITIONS local phi != 0, cylinder invariance, Brinkmann ansatz")
