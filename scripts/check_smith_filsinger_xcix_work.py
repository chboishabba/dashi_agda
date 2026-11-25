"""Exact separate restored work channels from the XCIX centred source solution."""
import hashlib,json
from pathlib import Path
from fractions import Fraction as F
import check_smith_filsinger_xcix_centered as c
raw=Path(c.__file__).read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='bd45db7d88d17f6369248efe2c82bf2b98e6ffa7'
d=c.d; rows=(0,1,6,7,8,9,10,11,14,15,16); sums={j:F(0) for j in rows}; defects=sums.copy();tails=sums.copy();gain=sums.copy()
for n in range(1,d.Nmax+1):
 wl=5*d.pl*n;wu=5*d.pu*n;w=(wl+wu)/2;we=(wu-wl)/2
 wp=[w**k for k in range(25)];der=[F(0)]+[k*wu**(k-1)*we for k in range(1,25)];dl,_=d.mag(d.c,wp,der);assert dl>0
 if n<=c.L:
  p=c.horner(d.c,w);pd=c.err(d.c,wu,we);src=c.div(c.add((F((-1)**n),F(0)),c.neg(c.phase[n%4])),(F(0),2*c.pi*n));se=c.ab(src)*c.pe/d.pl
 for j in rows:
  _,vh=d.mag(d.polys[j][1],wp,der);gain[j]=max(gain[j],d.up(wu*vh/dl))
  if n<=c.L:
   u=c.div(c.horner(d.polys[j][0],w),p);v=c.div(c.horner(d.polys[j][1],w),p)
   ue=(c.err(d.polys[j][0],wu,we)+c.ab(u)*pd)/dl;ve=(c.err(d.polys[j][1],wu,we)+c.ab(v)*pd)/dl
   z=c.add(c.mul(u,src),c.neg(c.mul(c.mul((F(0),w),v),c.non[n])))
   zr=tuple(d.low(k) for k in z);sums[j]+=2*c.sq(zr)
   defects[j]+=2*d.up(ue*(c.ab(src)+se)+c.ab(u)*se+(wu*ve+we*c.ab(v))*c.ab(c.non[n])+F(2,10**12))
  else:
   _,uh=d.mag(d.polys[j][0],wp,der);tails[j]+=d.up(2*uh/(d.pl*n*dl))
 if n%64==0:print('work harmonic',n,flush=True)
for j in rows:
 tails[j]+=d.up(sum(2*abs(v)/(d.pl*(5*d.pl)**(k+1)*(k+1)*d.Nmax**(k+1)*(1-d.rho)) for k,v in enumerate(d.polys[j][0])))
 gain[j]=max(gain[j],d.up(sum(abs(v)/d.wmin**k for k,v in enumerate(d.polys[j][1]))/(1-d.rho)))
# True reconstructed nonlinear difference bounded by gain times Lipschitz of N.
# All residuals real, conjugate-paired and zero mean, hence l2 <= l1/sqrt(2).
bounds={}
for j in rows:
 dist=defects[j]+tails[j]+gain[j]*d.lip*c.eps
 _,er=d.sqrtbounds(dist*dist/2);cl,ch=d.sqrtbounds(sums[j]);mean=d.fr(d.mean[j]);bounds[j]=(mean*mean+max(F(0),cl-er)**2,mean*mean+(ch+er)**2)
# Express each work channel as fraction of unchanged incident average power 1/4.
def combine(entries):return tuple(sum(4*k*bounds[j][i] for j,k in entries) for i in (0,1))
channels={'ohmic':combine([(0,F(1,5)),(1,F(1,5))]),'material_relaxation':combine([(6,F(4,9)),(7,F(4,9))]),'boundary_heat':combine([(8,F(20,9)),(9,F(20,9))]),'copper':combine([(10,F(35,100)),(11,F(28,100))]),'field_internal':combine([(14,F(4,10000)),(15,F(4,10000))]),'hf_coil':combine([(16,F(5,100))]),'hf_useful':(c.lo,c.hi)}
channels['reflected']=(1-sum(v[1] for v in channels.values()),1-sum(v[0] for v in channels.values()));assert channels['reflected'][0]>=0
# Lossless periodic diplexer signed interface transfer equals original circuit heat + load.
channels['signed_interface_work']=tuple(sum(channels[k][i] for k in ('copper','field_internal','hf_coil','hf_useful')) for i in (0,1))
print('WORK '+json.dumps(dict(status='EXACT_RESTORED_WORK_CHANNELS',intervals={k:[str(d.low(v[0])),str(d.up(v[1]))] for k,v in channels.items()},approx={k:list(map(float,v)) for k,v in channels.items()},bank_bleed=0,diodes=0,spark_heat=0,delay_storage_change=0,controller_work=0,physical=False,original_J36=False,CI=False)),flush=True)
