"""Tree-level universal hypermultiplet, Ferrara--Sabharwal convention.
Conditional spatial fixed-flux inverse, not an identified material or gravity solution.
"""
import sympy as s
D,X,Z,p=s.symbols('D X Z sigma',real=True)
j,k=s.symbols('j k',real=True)
e=s.exp(-D)
G=s.Matrix([[1,0,0,0],[0,e,0,0],[0,0,e+e**2*X**2,-e**2*X],[0,0,-e**2*X,e**2]])
assert s.simplify(G.det()-e**4)==0
block=G[2:4,2:4]; flux=s.Matrix([k,j]); v=s.simplify(block.inv()*flux)
assert s.simplify(v[0]-s.exp(D)*(k+X*j))==0
Rflux=-s.exp(2*D)*j*j/2-s.exp(D)*(k+X*j)**2/2
assert s.simplify(Rflux+(flux.T*block.inv()*flux)[0]/2)==0
# A common, illustrative stabilizing potential, same for both branches.
# e^(4D) prevents runaway at large positive D; D² confines negative D.
U=X**4/4+s.exp(4*D)/4+D/2+D**2
R=s.simplify((U+Rflux).subs({j:1,k:0}))
for x in [-1,1]:
 at={D:0,X:x}; assert all(s.diff(R,q).subs(at)==0 for q in (D,X))
 H=s.hessian(R,(D,X)).subs(at); assert H.is_positive_definite
 print('branch',x,'Hessian',H,'det',H.det(),'energy',R.subs(at))
# complete square: R=(X²-exp(D))²/4 + exp(4D)/4-3exp(2D)/4+D/2+D²
assert s.simplify(R-((X**2-s.exp(D))**2/4+s.exp(4*D)/4-3*s.exp(2*D)/4+D/2+D**2))==0
# exact target Ricci tensor
q=(D,X,Z,p); I=G.inv(); n=4
C=[[[s.simplify(sum(I[i,l]*(s.diff(G[l,b],q[a])+s.diff(G[l,a],q[b])-s.diff(G[a,b],q[l]))/2 for l in range(n))) for b in range(n)] for a in range(n)] for i in range(n)]
Ric=s.Matrix(n,n,lambda a,b:s.simplify(sum(s.diff(C[i][a][b],q[i])-s.diff(C[i][a][i],q[b])+sum(C[i][i][l]*C[l][a][b]-C[i][b][l]*C[l][a][i] for l in range(n)) for i in range(n))))
assert s.simplify(Ric+s.Rational(3,2)*G)==s.zeros(4)
print('full target Ricci scalar',s.simplify(s.trace(I*Ric)))
print('PASS source metric, flux inverse, common bounded potential and both local minima')
