#!/usr/bin/env python3
"""Exact 4+1 KK magnetic fixture; not a universal Einstein-Maxwell theorem.
(t,x,y,z,w), g=diag(-1,1,1,1), phi=kappa=1, A_y=b*x.
"""
import sympy as s

b,x=s.symbols("b x",real=True)
A=s.Matrix([0,0,b*x,0])
g=s.diag(-1,1,1,1)
G=(g+A*A.T).row_join(A).col_join(s.Matrix([[*A,1]]))
Gi=s.simplify(G.inv())
n=5
d=lambda f,i:s.diff(f,x) if i==1 else s.Integer(0)
Gamma=[[[s.simplify(sum(Gi[a,l]*(d(G[l,j],i)+d(G[l,i],j)-d(G[i,j],l)) for l in range(n))/2) for j in range(n)] for i in range(n)] for a in range(n)]
Ric=s.Matrix(n,n,lambda i,j:s.factor(sum(d(Gamma[k][i][j],k)-d(Gamma[k][i][k],j)+sum(Gamma[k][k][l]*Gamma[l][i][j]-Gamma[k][j][l]*Gamma[l][i][k] for l in range(n)) for k in range(n))))
R=s.factor(s.trace(Gi*Ric))
F=s.Matrix(4,4,lambda i,j:d(A[j],i)-d(A[i],j))
Fup=g.inv()*F*g.inv()
F2=s.simplify(sum(F[i,j]*Fup[i,j] for i in range(4) for j in range(4)))
assert s.simplify(G.det()+1)==0
assert s.simplify(R+F2/4)==0
assert s.simplify(Ric[4,4]-F2/4)==0
assert all(s.simplify(Ric[i,4]-A[i]*Ric[4,4])==0 for i in range(4))
assert s.simplify(F2-2*b*b)==0
print("PASS 4+1 metric: detG=-1, R5=-F²/4=-b²/2, R55=F²/4=b²/2")
print("NONVACUUM for b != 0: constant fibre radius with magnetic field violates R55=0")
print("NOT established: universal Ricci decomposition, full Einstein-Maxwell PDE")
