#!/usr/bin/env python3
"""Exact 5D warped-circle metric check, A=0, g4 flat Lorentz, phi=phi(x).
Computes Christoffels and Ricci directly rather than assuming KK formula.
"""
import sympy as s
x=s.symbols('x', real=True)
p=s.Function('phi')(x)
G=s.diag(-1,1,1,1,p**2)
Gi=s.diag(-1,1,1,1,1/p**2)
n=5
def d(expr,i): return s.diff(expr,x) if i==1 else s.S.Zero
Gamma=[[[s.simplify(sum(Gi[a,l]*(d(G[l,j],i)+d(G[l,i],j)-d(G[i,j],l)) for l in range(n))/2) for j in range(n)] for i in range(n)] for a in range(n)]
Ric=s.Matrix(n,n,lambda i,j:s.factor(sum(d(Gamma[k][i][j],k)-d(Gamma[k][i][k],j)+sum(Gamma[k][k][l]*Gamma[l][i][j]-Gamma[k][j][l]*Gamma[l][i][k] for l in range(n)) for k in range(n))))
R=s.factor(s.trace(Gi*Ric))
assert s.simplify(R+2*s.diff(p,x,2)/p)==0
assert s.simplify(Ric[1,1]+s.diff(p,x,2)/p)==0
assert s.simplify(Ric[4,4]+p*s.diff(p,x,2))==0
assert s.simplify(G.det()+p**2)==0
print('PASS exact variable-radion 4+1 Ricci: R5=-2 phi_xx/phi; Rxx=-phi_xx/phi; R55=-phi phi_xx')
