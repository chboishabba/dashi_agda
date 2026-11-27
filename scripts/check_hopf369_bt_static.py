import sympy as s
x,y,z,t,h=s.symbols('x y z t h', real=True); X=s.Matrix([x,y,z]); e=s.Matrix([0,0,1]); R=X.dot(X); coords=list(X)
# Actual BN3 pullback, through cubic order; h=4/5 on AK.
h=s.Rational(4,5); F0=2/h
# W= (delta^4-F^2 r^2)e+2F^2 z X+2F delta^2 e cross X
W=e*(1-(4+F0**2)*R)+2*F0**2*z*X+2*F0*(1-R)*e.cross(X)
# a=2 eps delta [F delta I+(4delta/h+4F)xx^T] W/D^2
# F delta = F0 + O(r^4); delta/D^2 = 1+(7-2F0^2)r^2 + O(r^4)
def trunc(p,n):
    return s.Add(*(term for term in s.expand(p).as_ordered_terms() if s.Poly(term,*coords).total_degree()<=n))
a=(2*(1+(7-2*F0**2)*R)*(F0*W+(4/h+4*F0)*X*(X.dot(W)))).applyfunc(lambda p:trunc(p,3))
# independent rational jet replay
D=(1-R)**4+(F0*(1+R))**2*R; F=F0*(1+R); d=1-R
Wfull=(d**4-F**2*R)*e+2*F**2*z*X+2*F*d**2*e.cross(X)
af=2*d*(F*d*Wfull+(4*d/h+4*F)*X*(X.dot(Wfull)))/D**2
for i in range(3):
    q=af[i].subs(dict(zip(coords,[t*x,t*y,t*z])), simultaneous=True)
    assert s.expand(s.series(q,t,0,4).removeO().subs(t,1)-a[i])==0
# H3 gamma=4/(h^2 delta^2) I; Gamma^k_ij=delta^k_i L_j+delta^k_j L_i-delta_ij L_k.
# L_i=2x_i+O(r^3), sufficient to second jet of M.
def G(k,i,j):return 2*((coords[j] if k==i else 0)+(coords[i] if k==j else 0)-(coords[k] if i==j else 0))
M=s.Matrix(3,3,lambda i,j:trunc(-(s.diff(a[j],coords[i])+s.diff(a[i],coords[j]))/2+sum(G(k,i,j)*a[k] for k in range(3)),2))
# inverse conformal gamma through required order, div M = gamma^jk nabla_j M_ki
iv=h**2/4*(1-2*R)
div=s.Matrix([trunc(iv*sum(s.diff(M[j,i],coords[j])-sum(G(k,j,j)*M[k,i]+G(k,j,i)*M[j,k] for k in range(3)) for j in range(3)),1) for i in range(3)])
zero={x:0,y:0,z:0}
cur=s.diff(div[1],x)-s.diff(div[0],y)
print('Hopf linear wall shear at origin:',M.subs(zero))
print('d(div M)_xy at origin:',cur)
assert cur!=0
# reference static lapse N0=(1+r²)/(1-r²); gradient log N0=4x+O(r³).
# M=0 at origin; derivative of symmetric tensor times grad log N0 has zero exterior derivative there.
assert M.subs(zero)==s.zeros(3)
# mean pure tension and static mixed Hessian imply
# d rho+4 rho dlog N0 = -div M0-(M0+tr(M0) I) dlog N0.
# scalar rho is ANY first-order isotropic conformal correction; multiply by N0^4 to remove it.
N=(1+R)/(1-R); logN=s.Matrix([s.diff(N,q)/N for q in coords]); ginv=h**2/4*(1-R)**2
m=ginv*s.trace(M)
forcing=-div-(ginv*M+m*s.eye(3))*logN
# exterior derivative at origin, exact without simplifying full rational expression
res=(s.diff(N**4*forcing[1],x)-s.diff(N**4*forcing[0],y)).subs(zero)
assert res==-cur and res!=0
print('static smooth-branch obstruction d(N0^4 forcing)_xy:',res)
# Actual AK weighted zero-mode conormal transport (b=4/5 cosh(y-log2)).
u=s.symbols('u',real=True); B=(s.Rational(5,4))**4*2*(s.Rational(3,5)-s.Rational(3,5)**3/3)
assert B==s.Rational(165,64)
A=s.Matrix([[1,B],[0,1]]); J=s.Matrix([[0,1],[-1,0]])
assert A.T*J*A==J
print('AK zero-mode transfer B=',B,'mean conormal / signed jump=',-1/B)
# Complex symmetric conormal generator with n=2 non-diagonal matrices, algebraic Green pairing.
a,b,c,d,e1,f=s.symbols('a b c d e f'); Ai=s.Matrix([[a,b],[b,c]]); V=s.Matrix([[d,e1],[e1,f]]); I=s.eye(2); O=s.zeros(2); J=O.row_join(I).col_join((-I).row_join(O)); H=O.row_join(Ai).col_join(V.row_join(O)); assert H.T*J+J*H==s.zeros(4)
print('PASS rational Hopf jets, static seam obstruction, AK zero mode and block Green identity')
# Arbitrary positive reference lapse: only its value and gradient enter the
# xy obstruction, because M(0)=0. Normalize its value to one.
g1,g2,g3=s.symbols('g1 g2 g3',real=True); g=s.Matrix([g1,g2,g3]); Njet=1+g.dot(X)
Fjet=-div-(h**2/4*M+m*s.eye(3))*g
res_general=(s.diff(Njet**4*Fjet[1],x)-s.diff(Njet**4*Fjet[0],y)).subs(zero)
assert res_general==-340
print('PASS arbitrary positive reference lapse gradient:',res_general)
