import sympy as s
# Exact restricted determinant via Schur complement, not ambient determinant.
t,u=s.symbols('t u', real=True)
A=s.Matrix([[4,1,0],[1,3,1],[0,1,2]])
Q=s.Matrix([[1,2,0]])
C=s.Matrix([[-2,0],[1,0],[0,1]])
assert Q*C==s.zeros(1,2)
Qp=s.Matrix([[0,1,2]]); Qq=s.Matrix([[0,2,-1]])
At=s.Matrix([[1,2,0],[2,0,1],[0,1,1]])
Au=s.Matrix([[0,1,1],[1,2,0],[1,0,1]])
Qt=Q+t*Qp+u*Qq
Ct=s.Matrix([[-Qt[1],-Qt[2]],[1,0],[0,1]])
Atu=A+t*At+u*Au
H=Ct.T*Atu*Ct; M=Ct.T*Ct
base={t:0,u:0}
def mixed_logdet(H):
 G=H.subs(base).inv(); X=H.diff(t).subs(base); Y=H.diff(u).subs(base); Z=H.diff(t,u).subs(base)
 d=H.det(); direct=(d.diff(t,u)/d-d.diff(t)*d.diff(u)/d**2).subs(base)
 r=s.trace(G*Z-G*X*G*Y)
 assert r==direct
 return r
r=(mixed_logdet(H)-mixed_logdet(M))/2
K=Atu.row_join(Qt.T).col_join(Qt.row_join(s.zeros(1)))
assert s.expand(H.det()*(Qt*Qt.T).det()+K.det()*M.det())==0
assert r==(mixed_logdet(K)-mixed_logdet(Qt*Qt.T))/2
R=s.Matrix([[1+t, u],[t*u,1+2*u]])
assert (mixed_logdet(R.T*H*R)-mixed_logdet(R.T*M*R))/2==r
O=s.Matrix([[1-t*t,-2*t,0],[2*t,1-t*t,0],[0,0,1+t*t]])/(1+t*t)
assert s.simplify(O.T*O)==s.eye(3)
Ag=O*A*O.T; Qg=Q*O.T; Cg=O*C
assert s.simplify(Qg*Cg)==s.zeros(1,2)
assert s.simplify(Cg.T*Ag*Cg)==C.T*A*C
assert s.simplify(Cg.T*Cg)==C.T*C
print('PASS restricted two-jet, induced volume, KKT BIDI, tangential basis, pure gauge transport; normal-motion mixed coefficient',r)
