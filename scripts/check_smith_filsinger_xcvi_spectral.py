"""XCVI native linear harmonic ceilings and passive LC diplexer diagnostic."""
import json
import sympy as S
import numpy as np
Q=S.Rational
s=S.symbols('s'); w2=S.symbols('w2',nonnegative=True)
ih=Q(52,100)+Q(12,100)*s;u=-(1+(Q(15,100)*s+Q(5,100))*ih)/2
Zi=Q(28,100)+Q(3,2)*s-Q(9,25)*s*s/(2*s+Q(35,100))
v=S.cancel((u+Zi*s*u)/(1+Q(31,20)*Zi*s));j=S.cancel(s*(-u+Q(31,20)*v));i=S.cancel(-Q(3,5)*s*j/(2*s+Q(35,100)));q=S.cancel((s*(Q(7,5)*u-v)+j-2*ih)/Q(35,100))
assert S.cancel((2*s+Q(35,100))*i+Q(3,5)*s*j)==0
assert S.cancel(u-v-Q(3,5)*s*i-(Q(3,2)*s+Q(28,100))*j)==0
assert S.cancel(s*(-u+Q(31,20)*v)-j)==0
assert S.cancel(s*(Q(7,5)*u-v)+j-Q(35,100)*q-2*ih)==0
assert S.cancel((Q(15,100)*s+Q(5,100))*ih+1+2*u)==0
assert S.cancel(ih-Q(52,100)-Q(12,100)*s)==0
def abs2(t):return S.cancel(t*t.subs(s,-s)).subs(s**2,-w2).cancel()
# Normalize cap voltage to 1; r coordinate can be chosen zero by unconstrained complex effort.
loss=S.cancel(Q(52,100)+Q(5,100)*abs2(ih)+Q(35,100)*abs2(i)+Q(28,100)*abs2(j)+Q(4,10000)*abs2(q));lam=S.cancel(Q(52,100)/loss)
assert lam.subs(w2,0)==Q(122500,126517)
num,den=[S.Poly(p,w2) for p in S.fraction(lam)];y=S.symbols('y')
assert all(v>=0 for v in S.Poly(den.as_expr().subs(w2,y+246),y).all_coeffs())
nd=den.as_expr().diff(w2)*num.as_expr()-num.as_expr().diff(w2)*den.as_expr()
assert all(v>=0 for v in S.Poly(nd.subs(w2,y+246),y).all_coeffs())
def atan_bounds(t,n):
 a=sum((-1)**k*t**(2*k+1)/Q(2*k+1) for k in range(n));b=a+(-1)**n*t**(2*n+1)/Q(2*n+1);return min(a,b),max(a,b)
a,b=atan_bounds(Q(1,5),16);c,d=atan_bounds(Q(1,239),5)
pl=Q(314159,100000);pu=Q(314160,100000);assert pl<16*a-4*d and 16*b-4*c<pu
upper=lam.subs(w2,0)/4;lower=upper
for n in range(1,9):
 k=0 if n%4==0 else 8 if n%2==0 else 4
 upper+=k/(pl*pl*n*n)*lam.subs(w2,(5*pl*n)**2);lower+=k/(pu*pu*n*n)*lam.subs(w2,(5*pu*n)**2)
upper+=lam.subs(w2,(5*pl*9)**2) # tail power fraction <= 1
assert upper<Q(36357,100000)
# Exact arbitrary-state lossless six-state diplexer storage balance.
E,id,vd,ia,vc,va,io,m,jd,ja=S.symbols('E id vd ia vc va io m jd ja',real=True)
assert S.expand(id*(E-vd)+vd*(id-jd)+ia*(m*E-vc-va)+vc*ia+va*(ia-io-ja)+io*va-E*(id+m*ia)+vd*jd+va*ja)==0
# Numerical candidate: same XCV scalar pulse and characteristic admittance; six passive states added.
M=S.Matrix([[2,Q(3,5)],[Q(3,5),Q(3,2)]]);N=S.Matrix([[Q(7,5),-1],[-1,Q(31,20)]])
z=S.Matrix(S.symbols('i j u v b q r ih x',real=True));i,j,u,v,b,q,r,ih,x=z
f=(M.inv()*S.Matrix([-Q(35,100)*i,u-v-Q(28,100)*j])).col_join(N.inv()*S.Matrix([-j+Q(35,100)*q+2*ih,j])).col_join(S.Matrix([-Q(18,1000)*b/Q(65,100),Q(11,10)*r-Q(2,10000)*q-Q(35,100)*u/2,-Q(11,10)*q-Q(2,10000)*r,(-x-Q(5,100)*ih-2*u)/Q(15,100),(ih-Q(52,100)*x)/Q(12,100)]))
A=f.jacobian(z);K=S.zeros(2,9);K[0,5]=K[1,6]=1
An=np.array(A,float);Kn=np.array(K,float);C=np.array([[1.,-1.],[0.,1.]])
Z0=-.015*Kn@np.linalg.solve(An,Kn.T);U0=np.linalg.solve(-An,Kn.T)[-1];d=np.linalg.solve((Z0+Z0.T)/2,U0);d/=np.linalg.norm(d);t=300*d;e=np.array([0.,1.]);Y=.2*np.eye(2)+20/9*C@C.T+np.outer(e,e)*(t@((Z0+Z0.T)/2)@t);B=Y@e/np.sqrt(Y[1,1]);
p=[0.05062544010579979,1.693920383568875,2.3560191376414155,-1.9312719391871591,-3.706267075904543,1.3457281077477645,-4.189915383847338,-0.8299539509959512,1.2222486178553746]
n=np.array([np.cos(p[0]),np.sin(p[0])])*10**p[1];m=10**p[2];Ld,Cd,Ls,Cs,Co,Lo=10**np.array(p[3:]);T=np.column_stack((t,n))
def native(w):
 s=1j*w;X=np.linalg.solve(s*np.eye(9)-An,np.sqrt(.03)*Kn.T/2);Z=np.sqrt(.03)*Kn@X;M=(2*s+.2+1.5*s/(s*s+2/3*s+4))*np.eye(2)+C@C.T/(1.5*s+1/(.1*s+20/9))+Y;return s,X,Z,M
def solve(w):
 s,X,Z,M=native(w)
 if w==0:
  E=np.linalg.solve(M+np.outer(e,e)*(t@Z@t),2*B);return X@t*(e@E)
 zd=1/(s*Ld);za=1/(s*Ls+1/(s*Cs));g=np.column_stack((zd*e,m*za*e));mat=np.zeros((4,4),complex);mat[:2,:2]=M+(zd+m*m*za)*np.outer(e,e);mat[:2,2:]=-g;mat[2:,:2]=-g.T;mat[2:,2:]=np.diag([s*Cd+zd,s*Co+1/(s*Lo)+za])+T.T@Z@T
 v=np.linalg.solve(mat,np.r_[2*B,0.,0.]);return X@T@v[2:]
ns=np.arange(1,257);X=np.array([solve(5*np.pi*n) for n in ns]);x0=solve(0).real/4;etas=.52*abs(X[:,-1])**2
ak=.25*np.sinc(ns/4)*np.exp(-2j*np.pi*ns*.625);tr=x0[:,None]+2*np.real((X.T*ak)@np.exp(2j*np.pi*ns[:,None]*np.linspace(0,1,4097)))
eta_dc=.52*x0[-1]**2*4;eta_ac=np.sum(.5*np.sinc(ns/4)**2*etas);gap=float(np.max(tr[2:4]-tr[4]));
print(json.dumps(dict(status='EXACT_LINEAR_INTRINSIC_BOUND_AND_PASSIVE_LC_IDENTITY_NUMERICAL_DIAGNOSTIC',lambda_dc=str(lam.subs(w2,0)),lambda_first=float(lam.subs(w2,(5*np.pi)**2)),lambda_second=float(lam.subs(w2,(10*np.pi)**2)),ideal_envelope_lower=float(lower),ideal_envelope_upper=float(upper),ideal_upper_exact=str(upper),dc=float(eta_dc),ac=float(eta_ac),total=float(eta_dc+eta_ac),first_harmonic=float(etas[0]),sampled_diode_gap=gap,sampled_cap_max=float(np.max(abs(tr[-1]))),log_params=p,harmonics=256,nonlinear_admission=False,physical_admission=False),indent=2))
