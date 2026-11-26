"""Original VHF density / collision-independent tensor envelope, and tilted Maxwell identity.
No calibrated field, atmospheric control, or ground-work prediction.
Usage: python check.py /path/to/original/files
"""
import sys,json,hashlib
from pathlib import Path
from datetime import datetime,timezone
import numpy as np
import h5py
import sympy as s
from pyproj import Transformer
# Single-species normalized tensor coordinates p=x/(1+x²), h=sign/(1+x²).
x=s.symbols('x',nonnegative=True,real=True); p=x/(1+x*x); h=1/(1+x*x)
assert s.simplify(p*p+(h-s.Rational(1,2))**2-s.Rational(1,4))==0
# Tilted anisotropic planar Maxwell elimination (e^-iwt, exp(ikx*x)).
def tilted(w,k,mu,eps):
    w,k,mu=map(s.sympify,(w,k,mu)); I=s.I
    L=s.Matrix([[1,0,0,0],[0,1,0,0],[-eps[2,0]/eps[2,2],-eps[2,1]/eps[2,2],0,-k/(w*eps[2,2])]])
    ez=L[2,:]; ex=s.Matrix([[1,0,0,0]]); ey=s.Matrix([[0,1,0,0]])
    hx=s.Matrix([[0,0,1,0]]); hy=s.Matrix([[0,0,0,1]])
    M=(I*w*mu*hy+I*k*ez).col_join(-I*w*mu*hx).col_join(I*k*k/(w*mu)*ey-I*w*eps[1,:]*L).col_join(I*w*eps[0,:]*L)
    return M,L
J=s.Matrix([[0,-1],[1,0]]); G=s.zeros(2).row_join(-J/2).col_join((J/2).row_join(s.zeros(2)))
# Real orthogonal rational rotation; complex material with tilted parallel axis.
R=s.Matrix([[s.Rational(3,5),0,s.Rational(4,5)],[0,1,0],[-s.Rational(4,5),0,s.Rational(3,5)]])
assert R.T*R==s.eye(3)
base=s.Matrix([[2+s.I,s.I/3,0],[-s.I/3,3+2*s.I,0],[0,0,4+3*s.I]])
for eps in [base,R*base*R.T,R*s.diag(2,3,4)*R.T]:
    M,L=tilted(2,1,1,eps); D=2*L.H*((eps-eps.H)/(2*s.I))*L
    assert (M.H*G+G*M+D).applyfunc(s.simplify)==s.zeros(4)
    A=s.eye(4)-M/10; U=A.inv()*(s.eye(4)+M/10)
    assert (G-U.H*G*U-A.inv().H*D*A.inv()/5).applyfunc(s.simplify)==s.zeros(4)
M,_=tilted(2,1,1,base)
expected=s.Matrix([[0,0,0,s.I*(2-1/(2*base[2,2]))],[0,0,-2*s.I,0],[-2*s.I*base[1,0],s.I*(s.Rational(1,2)-2*base[1,1]),0,0],[2*s.I*base[0,0],2*s.I*base[0,1],0,0]])
assert (M-expected).applyfunc(s.simplify)==s.zeros(4)
# Original radar observations, fixed screen from preceding replay.
path=Path(sys.argv[1])/'MAD6400_2017-12-18_bella_60@vhf.hdf5'; sha=hashlib.sha256(path.read_bytes()).hexdigest();assert sha=='d62180251bf74884910831c522ada43d9bec084d3f9ca6323f67c575ee05708d'
with h5py.File(path) as f:a=f['Data/Table Layout'][:]
t0=datetime(2017,12,18,2,30,tzinfo=timezone.utc).timestamp();a=a[(a['ut1_unix']<t0+12600)&(a['ut2_unix']>t0)]
g=(a['gfit']==0)&(a['ne']>0)&(a['dne']/a['ne']<.5)&(a['chisq']<10)&(a['ti']>50)&((a['gdalt']>=95)|(a['ne']<1e12)); assert sum(g)==7452
mid=(a['ut1_unix']+a['ut2_unix'])/2-t0; e=1.602176634e-19
# Quasineutral singly charged or charge-balanced positive ions/electrons only:
# B*sqrt(sigmaP²+sigmaH²) <= e*ne; units C/m³. No B assumed.
rows=[]
for lo,hi in [(80,100),(100,120),(120,150),(150,180),(180,200)]:
    stats=[]
    for l,r in [(0,2700),(2700,10800),(10800,12600)]:
        b=a[g&(a['gdalt']>=lo)&(a['gdalt']<hi)&(mid>=l)&(mid<r)]
        stats.append(dict(n=len(b),median_Bsigma_cap_C_m3=float(np.median(e*b['ne'])),median_Bsigma_cap_plus_reported_DNE_C_m3=float(np.median(e*(b['ne']+b['dne'])))))
    rows.append(dict(altitude_km=[lo,hi],windows=stats))
# Conditional straight geometric ray, rounded official Madrigal site metadata.
# Compare archived GDALT; not a certified original range/beam model.
fwd=Transformer.from_crs(4979,4978,always_xy=True); inv=Transformer.from_crs(4978,4979,always_xy=True)
lat,lon,alt=69.6,19.2,30.;latr,lonr=np.deg2rad([lat,lon]);site=np.array(fwd.transform(lon,lat,alt))
E=np.array([-np.sin(lonr),np.cos(lonr),0]);N=np.array([-np.sin(latr)*np.cos(lonr),-np.sin(latr)*np.sin(lonr),np.cos(latr)]);V=np.array([np.cos(latr)*np.cos(lonr),np.cos(latr)*np.sin(lonr),np.sin(latr)])
b=a[g&(a['gdalt']>=80)&(a['gdalt']<200)];az,el=np.deg2rad(b['azm']),np.deg2rad(b['elm']);ray=np.cos(el)[:,None]*(np.sin(az)[:,None]*E+np.cos(az)[:,None]*N)+np.sin(el)[:,None]*V; xyz=site+1000*b['range'][:,None]*ray
lons,lats,heights=inv.transform(*xyz.T);dh=heights/1000-b['gdalt'];assert np.isfinite(dh).all()
print(json.dumps(dict(status='CONDITIONAL_CONSTITUTIVE_GEOMETRY_ON_ORIGINAL_RADAR',sha256=sha,accepted=int(sum(g)),bands=rows,ray=dict(rows=len(b),latitude_deg=[float(min(lats)),float(max(lats))],longitude_deg=[float(min(lons)),float(max(lons))],altitude_difference_km_quantiles=np.percentile(dh,[0,50,100]).tolist()),tilted_fixtures=3,physical_admission=False),indent=2))
