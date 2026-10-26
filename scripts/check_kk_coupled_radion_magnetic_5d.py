#!/usr/bin/env python3
"""Independent 5D tensor audit with BOTH nonconstant radion and nonzero magnetic F.
Flat Lorentz base; phi(x) is arbitrary smooth; A_y=b*x; kappa=1.
Compare full Christoffel/Ricci scalar against the general KK identity.
"""
import sympy as s
x,b=s.symbols("x b",real=True)
p=s.Function("phi")(x)
A=s.Matrix([0,0,b*x,0]);g=s.diag(-1,1,1,1)
G=(g+p**2*A*A.T).row_join(p**2*A).col_join(s.Matrix([[*(p**2*A),p**2]]))
Gi=s.simplify(G.inv())
n=5
def d(f,i):return s.diff(f,x) if i==1 else s.S.Zero
C=[[[s.factor(sum(Gi[a,l]*(d(G[l,j],i)+d(G[l,i],j)-d(G[i,j],l)) for l in range(n))/2) for j in range(n)] for i in range(n)] for a in range(n)]
Ric=s.Matrix(n,n,lambda i,j:s.factor(sum(d(C[k][i][j],k)-d(C[k][i][k],j)+sum(C[k][k][l]*C[l][i][j]-C[k][j][l]*C[l][i][k] for l in range(n)) for k in range(n))))
R=s.factor(s.trace(Gi*Ric))
F2=2*b*b
expected=-p**2*F2/4-2*s.diff(p,x,2)/p
assert s.simplify(R-expected)==0,(R,expected)
assert s.simplify(G.det()+p**2)==0
assert s.simplify(R.subs({p:1,s.diff(p,x):0,s.diff(p,x,2):0})+b*b/2)==0
assert s.simplify(R.subs(b,0)+2*s.diff(p,x,2)/p)==0
print("PASS 5D coupled variable radion + nonzero magnetic F: full scalar curvature, determinant, both limits")
print("NOT a curved-base general theorem or a solution of the 5D vacuum equations")
if __name__=="__main__":pass
