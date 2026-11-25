"""XCVIII exact nearby diplexer certificate, no CI."""
import sympy as S
from fractions import Fraction as F
from math import isqrt
import json
Q=S.Rational
M=S.Matrix([[2,Q(3,5)],[Q(3,5),Q(3,2)]]);N=S.Matrix([[Q(7,5),-1],[-1,Q(31,20)]])
z=S.Matrix(S.symbols('i j u v q r ih x'));i,j,u,v,q,r,ih,x=z
f=(M.inv()*S.Matrix([-Q(35,100)*i,u-v-Q(28,100)*j])).col_join(N.inv()*S.Matrix([-j+Q(35,100)*q+2*ih,j])).col_join(S.Matrix([Q(11,10)*r-Q(2,10000)*q-Q(35,100)*u/2,-Q(11,10)*q-Q(2,10000)*r,(-x-Q(5,100)*ih-2*u)/Q(15,100),(ih-Q(52,100)*x)/Q(12,100)]))
Ac=f.jacobian(z);K=S.zeros(2,8);K[0,4]=K[1,5]=1
Wc=S.diag(M,N,2,2,Q(15,100),Q(12,100));Dc=S.diag(Q(35,100),Q(28,100),0,0,Q(4,10000),Q(4,10000),Q(5,100),Q(52,100));assert Ac.T*Wc+Wc*Ac==-2*Dc
ell=S.Matrix([Q(-36,25),Q(-6589440,126517)]);g=S.Matrix([Q('8.54917'),Q('.433176')]);a=Q('122.84358')
Ld,Cd,Ls,Cs,Co,Lo=map(Q,['.011714616','.00019666765','22.168081','.000064578004','.14792652','16.682019'])
Y=S.Matrix([[Q(209,45),-Q(20,9)],[-Q(20,9),36]]);assert Y.is_positive_definite
C=S.Matrix([[1,-1],[0,1]]);I=S.eye(2);A=S.zeros(24);B=S.zeros(24,1);B[:2,0]=Y[:,1]/6
A[:2,:2]=-(Q(1,5)*I+Y)/2;A[:2,2:4]=C/2;A[:2,6:8]=-I/2;A[2:4,:2]=-C.T/Q(3,2);A[2:4,8:10]=-I/Q(3,2);A[4:6,6:8]=I;A[6:8,:2]=Q(3,2)*I;A[6:8,4:6]=-4*I;A[6:8,6:8]=-Q(2,3)*I;A[8:10,2:4]=10*I;A[8:10,8:10]=-Q(200,9)*I;A[10:18,10:18]=Ac
A[1,18]=-Q(1,2);A[1,20]=-a/2;A[18,1]=1/Ld;A[18,19]=-1/Ld;A[19,18]=1/Cd;A[20,1]=a/Ls;A[20,21]=-1/Ls;A[20,22]=-1/Ls;A[21,20]=1/Cs;A[22,20]=1/Co;A[22,23]=-1/Co;A[23,22]=1/Lo
A[10:18,19]=K.T*ell/2;A[10:18,22]=K.T*g/2;A[19,10:18]=-ell.T*K/Cd;A[22,10:18]=-g.T*K/Co
W=S.diag(2,2,Q(3,2),Q(3,2),Q(8,3),Q(8,3),Q(2,3),Q(2,3),Q(1,10),Q(1,10),Wc,Ld,Cd,Ls,Cs,Co,Lo)
D=S.diag(Q(1,5)*I+Y,S.zeros(4),Q(4,9)*I,Q(20,9)*I,Dc,S.zeros(6));assert A.T*W+W*A==-2*D
mean=-A.inv(method='DM')*B/4;x0=mean[17];m=1+Q(3,2)*x0*x0;Fmat=A.copy();Fmat[17,:]/=m;ex=S.zeros(24,1);ex[17]=1/m
c=Fmat.charpoly().all_coeffs();V=B.row_join(ex);blocks=[]
for k in range(24):
 blocks.append(V);V=Fmat*V+c[k+1]*B.row_join(ex)
assert V==S.zeros(24,2)
def fr(x):return F(int(x.p),int(x.q))
c=list(map(fr,c));polys=[[list(map(fr,[v[j,k] for v in blocks])) for k in range(2)] for j in range(24)]
def at(t,n):
 a=sum((-1)**k*t**(2*k+1)/F(2*k+1) for k in range(n));b=a+(-1)**n*t**(2*n+1)/F(2*n+1);return min(a,b),max(a,b)
a,b=at(F(1,5),18);d,e=at(F(1,239),6);pl=F(3141592653589793238,10**18);pu=pl+F(1,10**18);assert pl<16*a-4*e and 16*b-4*d<pu
scale=10**12
def up(x):return F(-(-x.numerator*scale//x.denominator),scale)
def low(x):return F(x.numerator*scale//x.denominator,scale)
def sqrtbounds(x):
 z=isqrt(x.numerator*scale**2//x.denominator);return F(z,scale),F(z+1,scale)
def mag(p,wp,der):
 d=len(p)-1;re=F(0);im=F(0);de=F(0)
 for j,v in enumerate(p):
  k=d-j;term=v*wp[k]
  if k%2:im+=term*(-1 if k%4==3 else 1)
  else:re+=term*(-1 if k%4==2 else 1)
  if k:de+=abs(v)*der[k]
 s=max(abs(re),abs(im))
 if not s:return F(0),de
 l,h=sqrtbounds((re/s)**2+(im/s)**2)
 return max(F(0),l*s-de),h*s+de
Nmax=384;wmin=5*pl*(Nmax+1);rho=sum(abs(v)/wmin**j for j,v in enumerate(c) if j);assert rho<1
amp=[F(0)]*24;H=[F(0)]*24;firstlo=F(0)
for n in range(1,Nmax+1):
 wl=5*pl*n;wu=5*pu*n;wm=(wl+wu)/2;err=(wu-wl)/2;wp=[wm**k for k in range(25)];der=[F(0)]+[k*wu**(k-1)*err for k in range(1,25)];dl,du=mag(c,wp,der);assert dl>0
 al,au=sqrtbounds(F(0 if n%4==0 else 4 if n%2==0 else 2));au=0 if n%4==0 else au/(2*pl*n);al=al/(2*pu*n)
 for j in (12,13,17):
  l,h=mag(polys[j][0],wp,der);amp[j]+=up(2*au*h/dl)
  _,h=mag(polys[j][1],wp,der);H[j]=max(H[j],up(wu*h/dl))
  if j==17 and n==1:firstlo=low(al*l/du)
 if n%64==0:print('harmonic',n,flush=True)
for j in (12,13,17):
 amp[j]+=up(sum(2*abs(v)/(pl*(5*pl)**(k+1)*(k+1)*Nmax**(k+1)*(1-rho)) for k,v in enumerate(polys[j][0])))
 H[j]=max(H[j],up(sum(abs(v)/wmin**k for k,v in enumerate(polys[j][1]))/(1-rho)))
r=F(13,100);xq=fr(x0);Nbound=F(3,2)*abs(xq)*r*r+r**3/2;lip=3*abs(xq)*r+F(3,2)*r*r
mb=amp[17]+H[17]*Nbound;ct=H[17]*lip;guards=[fr(mean[j])+amp[j]+H[j]*Nbound for j in (12,13)]
print('mean',float(xq),'rho',float(rho),'amp',float(amp[17]),'H',float(H[17]),'map',float(mb),'contract',float(ct),'guards',list(map(float,guards)), 'first',float(firstlo),flush=True)
assert mb<r and ct<1 and max(guards)<F(1,10)
first=max(F(0),firstlo-H[17]*Nbound/2);elo=F(52,25)*(xq*xq+2*first*first);ehi=F(52,25)*(xq*xq+r*r)
print(json.dumps(dict(status='EXACT_NEARBY_DIPLEXER_WIENER_CERTIFICATE',mean_x=str(x0),radius=str(r),map_upper=str(up(mb)),contraction_upper=str(up(ct)),guard_upper=list(map(lambda x:str(up(x)),guards)),tail_dominance=str(up(rho)),first_harmonic_lower=str(low(first)),eta_lower=str(low(elo)),eta_upper=str(up(ehi)),eta_lower_float=float(elo),eta_upper_float=float(ehi),finite_harmonics=Nmax,physical_admission=False,original_J36=False),indent=2))
