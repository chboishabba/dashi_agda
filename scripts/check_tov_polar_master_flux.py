"""Fixed-radius polar canonical current in vacuum RW gauge; moving corners open.
Unit harmonic normalization and increasing-r canonical normal convention.
"""
import sympy as s
r,M,n=s.symbols('r M n',positive=True); F=1-2*M/r
V=2*F*(n*n*(n+1)*r**3+3*n*n*M*r*r+9*n*M*M*r+9*M**3)/(r**3*(n*r+3*M)**2)
A=(n*(n+1)*r*r+3*n*M*r+6*M*M)/(r*r*(n*r+3*M))
# independent P,Q,Ptt,Qtt, etc.; radial derivative of time jets via wave
p,q,a,b=s.symbols('p q a b'); dr=lambda u:s.diff(u,r)+s.diff(u,p)*q/F+s.diff(u,q)*(a+V*p)/F+s.diff(u,a)*b/F
K=A*p+q; H=s.cancel((n+3*M/r)*((n+1)*p/r-K)/F+r*dr(K)); H1t=r*b/F+(n*r*r-3*n*M*r-3*M*M)/((r-2*M)*(n*r+3*M))*a
G=s.diag(-F,r*r,r*r); I=G.inv(); K0=s.sqrt(F)*G.diff(r)/2
h=s.diag(F*H,r*r*K,r*r*K)
j=s.sqrt(F)/2*(h.diff(r)+h.diff(p)*q/F+h.diff(q)*(a+V*p)/F+h.diff(a)*b/F-H*G.diff(r)/2-s.diag(2*H1t,0,0))
# use angular factor sin theta Y^2 integrates to 1
DI=-I*h*I; tr=s.trace(I*K0); dt=s.trace(DI*K0+I*j)
pi=s.sqrt(F)*r*r*(s.trace(I*h)/2*(I*K0*I-tr*I)+DI*K0*I+I*j*I+I*K0*DI-dt*I-tr*DI)/(16*s.pi)
vs=[p,q,a,b]
C=s.zeros(4)
for i in range(4):
    for k in range(i+1,4):
        C[i,k]=s.factor(s.trace(pi.diff(vs[i])*h.diff(vs[k])-pi.diff(vs[k])*h.diff(vs[i])))
        C[k,i]=-C[i,k]
assert s.cancel(C[0,1]+n*(n+1)/(16*s.pi))==0
assert C[2,3]==0
D=C[:2,2:]
assert D==D.T
assert s.cancel(D[0,1]-r**3*A/(16*s.pi*F))==0
assert s.cancel(D[1,1]-r**3/(16*s.pi*F))==0
# For two master solutions X=(P,Q), cross block is X1^T D X2_tt
# minus X2^T D X1_tt = time derivative of corresponding first jets.
t=s.symbols('t'); X=s.Matrix([s.Function('X%d'%i)(t) for i in range(2)]); Y=s.Matrix([s.Function('Y%d'%i)(t) for i in range(2)])
assert s.expand((X.T*D*Y.diff(t)-Y.T*D*X.diff(t))[0].diff(t)-(X.T*D*Y.diff(t,2)-Y.T*D*X.diff(t,2))[0])==0
print('PASS polar canonical current, universal master coefficient, symmetric endpoint block')
print('OPEN moving embedding, physical junction range and full energy sign')
