"""Centred residual certificate on byte-pinned XCVIII, no time shooting."""
import hashlib,json
from pathlib import Path
from fractions import Fraction as F
import numpy as np
import check_smith_filsinger_xcviii_transfer_wiener as d
raw=Path(d.__file__).read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='9e6934afe640c9ffa43d880543de5341624767c8'
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[0],-a[1]
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def sc(a,s):return a[0]*s,a[1]*s
def sq(a):return a[0]**2+a[1]**2
def div(a,b):return sc(mul(a,(b[0],-b[1])),1/sq(b))
def ab(a):return d.sqrtbounds(sq(a))[1]
def horner(p,w):
 a=(F(0),F(0))
 for c in p:a=add(mul(a,(F(0),w)),(c,F(0)))
 return a
def err(p,wu,e):return sum(abs(c)*(len(p)-1-j)*wu**(len(p)-2-j)*e for j,c in enumerate(p[:-1]))
Z=(F(0),F(0));N=16;L=3*N;pi=(d.pl+d.pu)/2;pe=(d.pu-d.pl)/2
phase=[(F(1),F(0)),(F(0),F(1)),(F(-1),F(0)),(F(0),F(-1))]
lin={};H={};errors={}
for n in range(1,L+1):
 w=5*pi*n;we=5*pe*n;wu=w+we;p=horner(d.c,w);pd=err(d.c,wu,we);dl=d.sqrtbounds(sq(p))[0]-pd;assert dl>0
 src=div(add((F((-1)**n),F(0)),neg(phase[n%4])),(F(0),2*pi*n));se=ab(src)*pe/d.pl
 j=17;u=horner(d.polys[j][0],w);v=horner(d.polys[j][1],w);ur=div(u,p);vr=div(v,p)
 ue=(err(d.polys[j][0],wu,we)+ab(ur)*pd)/dl;ve=(err(d.polys[j][1],wu,we)+ab(vr)*pd)/dl
 lin[n]=mul(ur,src);H[n]=mul((F(0),w),vr)
 errors[n]=(d.up(ue*(ab(src)+se)+ab(ur)*se),d.up(wu*ve+we*ab(vr)))
a=np.zeros(2*N+1,complex);h=a.copy()
for n in range(1,N+1):
 a[N+n]=complex(*map(float,lin[n]));h[N+n]=complex(*map(float,H[n]));a[N-n]=a[N+n].conjugate();h[N-n]=h[N+n].conjugate()
v=a.copy()
for _ in range(32):
 nv=1.5*float(d.xq)*np.convolve(v,v)[N:3*N+1]+.5*np.convolve(np.convolve(v,v),v)[2*N:4*N+1];v=a-h*nv
center={0:Z}
for n in range(1,N+1):
 center[n]=tuple(F(round(float(k)*10**12),10**12) for k in (v[N+n].real,v[N+n].imag));center[-n]=(center[n][0],-center[n][1])
def conv(a,b):
 out={}
 for i,x in a.items():
  for j,y in b.items():out[i+j]=add(out.get(i+j,Z),mul(x,y))
 return out
v2=conv(center,center);v3=conv(v2,center);non={n:add(sc(v2.get(n,Z),F(3,2)*d.xq),sc(v3.get(n,Z),F(1,2))) for n in range(-L,L+1)}
cn=2*sum(ab(center[n]) for n in range(1,N+1));assert cn<d.r
# Beyond 3N, nonlinear convolution of the finite centre is identically zero.
tail=F(0)
for n in range(L+1,d.Nmax+1):
 wl=5*d.pl*n;wu=5*d.pu*n;wm=(wl+wu)/2;we=(wu-wl)/2;wp=[wm**k for k in range(25)];der=[F(0)]+[k*wu**(k-1)*we for k in range(1,25)];dl,_=d.mag(d.c,wp,der);assert dl>0
 _,hi=d.mag(d.polys[17][0],wp,der);tail+=d.up(2*hi/(d.pl*n*dl))
tail+=d.up(sum(2*abs(v)/(d.pl*(5*d.pl)**(k+1)*(k+1)*d.Nmax**(k+1)*(1-d.rho)) for k,v in enumerate(d.polys[17][0])))
res=tail
for n in range(1,L+1):
 errl,errh=errors[n];r=add(add(lin[n],neg(mul(H[n],non[n]))),neg(center.get(n,Z)));res+=2*(ab(r)+errl+errh*ab(non[n]))
eps=d.up(res/(1-d.ct));assert eps<F(1,1000)
center2=2*sum(sq(center[n]) for n in range(1,N+1));cl,ch=d.sqrtbounds(center2);_,er=d.sqrtbounds(eps*eps/2)
lo=F(52,25)*(d.xq*d.xq+max(F(0),cl-er)**2);hi=F(52,25)*(d.xq*d.xq+(ch+er)**2)
print('XCIX '+json.dumps(dict(status='EXACT_CENTERED_RECOVERY',center_modes=N,residual=str(d.up(res)),tail=str(d.up(tail)),distance=str(eps),center_norm=str(d.up(cn)),eta_lower=str(d.low(lo)),eta_upper=str(d.up(hi)),eta_lower_float=float(lo),eta_upper_float=float(hi),guard_bounds_retained=True,original_J36=False,physical=False,CI=False)),flush=True)
