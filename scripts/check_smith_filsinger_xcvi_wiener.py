"""Exact rational Fourier/Wiener certificate for nearby XCV rank-one candidate.
No numerical inverse is trusted: each finite resolvent uses exact Gaussian rational
arithmetic. Fourier tails use Neumann geometric bounds. Local SymPy only.
"""
import sympy as S
from fractions import Fraction as F
import json
Q=S.Rational
# Original off-state circuit, bank removed (exact periodic bank=0).
M=S.Matrix([[2,Q(3,5)],[Q(3,5),Q(3,2)]]); N=S.Matrix([[Q(7,5),-1],[-1,Q(31,20)]])
z=S.Matrix(S.symbols('i j u v q r ih x',real=True));i,j,u,v,q,r,ih,x=z
f=(M.inv()*S.Matrix([-Q(35,100)*i,u-v-Q(28,100)*j])).col_join(N.inv()*S.Matrix([-j+Q(35,100)*q+2*ih,j])).col_join(S.Matrix([Q(11,10)*r-Q(2,10000)*q-Q(35,100)*u/2,-Q(11,10)*q-Q(2,10000)*r,(-x-Q(5,100)*ih-2*u)/Q(15,100),(ih-Q(52,100)*x)/Q(12,100)]))
Ac=f.jacobian(z); K=S.zeros(2,8);K[0,4]=K[1,5]=1
Wc=S.diag(M,N,2,2,Q(15,100),Q(12,100)); Dc=S.diag(Q(35,100),Q(28,100),0,0,Q(4,10000),Q(4,10000),Q(5,100),Q(52,100));assert Ac.T*Wc+Wc*Ac==-2*Dc
Z=-Q(15,1000)*K*Ac.inv()*K.T; Zs=(Z+Z.T)/2; dr=Zs.inv()*(-Ac.inv()*K.T/2)[-1,:].T
ell=Q(-36,25)*dr/dr[0] # exact coupling kappa*T vector, near beta300
L=ell*S.Matrix([[0,1]]);C=S.Matrix([[1,-1],[0,1]]); I=S.eye(2)
Y=S.Matrix([[Q(209,45),-Q(20,9)],[-Q(20,9),36]]) # H0[0,0]=209/45
assert Y.is_positive_definite
A=S.zeros(18);B=S.zeros(18,1);B[:2,0]=Y[:,1]/6
A[:2,:2]=-(Q(1,5)*I+Y)/2;A[:2,2:4]=C/2;A[:2,6:8]=-I/2;A[2:4,:2]=-C.T/Q(3,2);A[2:4,8:10]=-I/Q(3,2);A[4:6,6:8]=I;A[6:8,:2]=Q(3,2)*I;A[6:8,4:6]=-4*I;A[6:8,6:8]=-Q(2,3)*I;A[8:10,2:4]=10*I;A[8:10,8:10]=-Q(200,9)*I;A[10:,10:]=Ac;A[:2,10:]=-L.T*K/2;A[10:,:2]=K.T*L/2
W=S.diag(2,2,Q(3,2),Q(3,2),Q(8,3),Q(8,3),Q(2,3),Q(2,3),Q(1,10),Q(1,10),Wc)
D=S.diag(Q(1,5)*I+Y,S.zeros(4),Q(4,9)*I,Q(20,9)*I,Dc);assert A.T*W+W*A==-2*D
mean=-A.inv()*B/4;x0=mean[-1];assert x0>0
m=1+Q(3,2)*x0*x0;Fmat=A.copy();Fmat[-1,:]=Fmat[-1,:]/m
ex=S.zeros(18,1);ex[-1]=1/m
# For v=x-x0, y=state-mean, equation y'=Fmat y+B(a-1/4)-ex*d/dt N(v), N=3*x0*v^2/2+v^3/2.
# Verify imaginary axis nonsingularity: exact rational Lyapunov test via energy
# semidefinite damping and observability (rank of stacked D F^k).
Wm=W.copy();Wm[-1,-1]*=m;assert Fmat.T*Wm+Wm*Fmat==-2*D
Obs=S.Matrix.vstack(*[D*Fmat**k for k in range(4)]);assert Obs.rank()==18
# Exact pi enclosure by Machin and alternating arctan series.
def atan_bounds(t,n):
 a=sum((-1)**k*t**(2*k+1)/Q(2*k+1) for k in range(n));b=a+(-1)**n*t**(2*n+1)/Q(2*n+1);return min(a,b),max(a,b)
a,b=atan_bounds(Q(1,5),16);c,d=atan_bounds(Q(1,239),5)
pl=Q(3141592653589793,10**15);pu=Q(3141592653589794,10**15);assert pl<16*a-4*d and 16*b-4*c<pu
p=(pl+pu)/2
# Exact complex l1 (|Re|+|Im|) gives upper bound on modulus. Matrix induced infinity.
def ab(z):
 re,im=z.as_real_imag();return abs(re)+abs(im)
def norm(A):return max(sum(ab(v) for v in A.row(i)) for i in range(A.rows))
def ceilq(x,scale=10**12):return Q(S.ceiling(x*scale),scale)
Nmax=16
amp=[Q(0)]*18;H=[Q(0)]*18
for n in range(1,Nmax+1):
 w=5*n*p;err=5*n*(pu-pl)/2
 # Inverse computed over QQ(i) via exact DomainMatrix.
 R=(S.I*w*S.eye(18)-Fmat).inv(method='DM');rn=ceilq(norm(R));assert err*rn<1
 rb=R*B;rh=R*ex;corr=err*rn/(1-err*rn)
 cb=ceilq(corr*norm(rb));ch=ceilq(corr*norm(rh))
 # |a_n| <= 1/(pi*n) (phase irrelevant), multiples of four vanish.
 aup=0 if n%4==0 else 1/(pl*n)
 for j in range(18):
  amp[j]+=ceilq(2*aup*(ab(rb[j])+cb))
  H[j]=max(H[j],ceilq((w+err)*(ab(rh[j])+ch)))
 print('n',n,flush=True)
# Tail of source response, use infinity norm Neumann; improve per-component
# with exact Krylov zeros and first finite coefficients.
F_norm=norm(Fmat);wmin=5*pl*(Nmax+1);assert F_norm<wmin
# 2*sum (|F^k B|/(pi n*(5pi n)^(k+1))) <= integral bound at Nmax.
Kmax=6;cur=B
for k in range(Kmax):
 for j in range(18):amp[j]+=ceilq(2*abs(cur[j])/(pl*(5*pl)**(k+1)*(k+1)*Nmax**(k+1)))
 cur=Fmat*cur
rem=2*norm(cur)/(pl*(5*pl)**(Kmax+1)*(Kmax+1)*Nmax**(Kmax+1)*(1-F_norm/wmin))
for j in range(18):amp[j]+=ceilq(rem);H[j]=max(H[j],ceilq(norm(ex)/(1-F_norm/wmin)))
# Contraction of scalar Fourier map on zero-mean real l1 radius r, with
# uniform H_n bound; N can have mean, but H_0=0 so map stays zero-mean.
r=Q(11,40000);Nbound=Q(3,2)*abs(x0)*r*r+r**3/2
lip=3*abs(x0)*r+Q(3,2)*r*r
print('x0',float(x0),'A norm',float(F_norm),'amp',list(map(float,amp)),'H',list(map(float,H)),flush=True)
print('map',float(amp[-1]+H[-1]*Nbound),'lip',float(H[-1]*lip))
assert amp[-1]+H[-1]*Nbound<r and H[-1]*lip<1
# Full state reconstructed from same scalar fixed point. Guard exclusion.
bounds=[amp[j]+H[j]*Nbound for j in range(18)];assert mean[12]+bounds[12]<Q(1,10) and mean[13]+bounds[13]<Q(1,10)
# Parseval: mean v=0, mean x^2 in [x0^2,x0^2+r^2]; incident average power 1/4.
eta_lo=4*Q(52,100)*x0*x0;eta_hi=4*Q(52,100)*(x0*x0+r*r)
print(json.dumps(dict(status='EXACT_WIENER_FIXED_POINT_GUARDS_AND_WORK_BOUND',nearby_candidate=True,ell=[str(v) for v in ell],Y=[[str(v) for v in row] for row in Y.tolist()],mean_x=str(x0),mean_x_float=float(x0),r=str(r),map_bound=float(amp[-1]+H[-1]*Nbound),contraction=float(H[-1]*lip),guards=[float(mean[j]+bounds[j]) for j in (12,13)],eta_lo=float(eta_lo),eta_hi=float(eta_hi),eta_lo_exact=str(eta_lo),eta_hi_exact=str(eta_hi),F_norm=float(F_norm),finite_harmonics=Nmax,amp_upper=[str(v) for v in amp],H_upper=[str(v) for v in H],physical_admission=False,original_J36=False),indent=2))
