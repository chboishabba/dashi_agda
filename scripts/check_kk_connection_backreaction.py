import sympy as s
K,H,M,a=s.symbols('K H M a',positive=True)
x=s.symbols('X',real=True); j,k=s.symbols('Jphi JZ',real=True)
G=s.Matrix([[K,-K*a*x],[-K*a*x,H+K*a*a*x*x]])
v=G.inv()*s.Matrix([j,k]); assert s.simplify(v[1]-(k+a*x*j)/H)==0
assert s.simplify(v[0]-j/K-a*x*v[1])==0
D,g,B=s.symbols('Delta gamma B',real=True)
U=D*x*x/2+g*x**4/4-B*x
R=U-(s.Matrix([j,k]).T*G.inv()*s.Matrix([j,k]))[0]/2
assert s.simplify(s.diff(R,x)-(s.diff(U,x)-a*j*(k+a*x*j)/H))==0
print('fixed flux Routh potential:',s.expand(R))
# fixed reference gradient in spherical support, Green self-energy from previous exact donor
V,l,b=s.symbols('V lambda b',positive=True)
S=l*l*V/(3*K); completion=l*l*V/K
assert s.simplify(completion-S-2*S)==0
print('fixed reference gradient completion minus Green self-response:',s.simplify(completion-S))
# inverse branch same fluxes, independent curvature tuning
for target in [-1,1]:
 fixture={K:1,H:1,a:1,j:1,k:s.Rational(1,10),g:1,B:0}
 r=R.subs(fixture); d=s.solve(s.diff(r,x).subs(x,target),D)[0]
 assert s.diff(r,x).subs({x:target,D:d})==0
 print('target',target,'bare curvature',d,'relaxed Hessian',s.diff(r,x,2).subs({x:target,D:d}))
# target-space metric ds²=M dX²+H dZ²+K(dphi-a X dZ)²; compute Ricci scalar
coords=[x,s.Symbol('Z'),s.Symbol('phi')]; metric=s.diag(M,H,K);metric[1,1]+=K*a*a*x*x;metric[1,2]=metric[2,1]=-K*a*x
iv=metric.inv(); n=3
C=[[[s.simplify(sum(iv[i,l]*(s.diff(metric[l,j],coords[k])+s.diff(metric[l,k],coords[j])-s.diff(metric[j,k],coords[l]))/2 for l in range(n))) for k in range(n)] for j in range(n)] for i in range(n)]
Ric=s.Matrix(n,n,lambda j,k:s.simplify(sum(s.diff(C[i][j][k],coords[i])-s.diff(C[i][j][i],coords[k])+sum(C[i][i][l]*C[l][j][k]-C[i][k][l]*C[l][j][i] for l in range(n)) for i in range(n))))
scalar=s.simplify(s.trace(iv*Ric)); assert scalar==-K*a*a/(2*H*M)
print('target-space Ricci scalar:',scalar)
print('PASS flux relaxation, inverse equilibria, completion debit and target curvature')
