"""Original radar observation fibres and conditional cold-Drude spectral weight.
No calibrated collision law, magnetic model, physical source flux or heating fit.
"""
import datetime as dt
import hashlib
import json
import sys
from pathlib import Path
import h5py
import numpy as np
import sympy as s
from scipy.constants import elementary_charge as e, electron_mass as me, atomic_mass as u, epsilon_0
root=Path(sys.argv[1])
t0=dt.datetime(2017,12,18,2,30,tzinfo=dt.timezone.utc).timestamp()
products={}
for k in (6300,6301,6302,6400):
    p=root/f'MAD{k}_2017-12-18_bella_60@vhf.hdf5'
    receipt=json.loads(p.with_suffix('.receipt.json').read_text())
    digest=hashlib.sha256(p.read_bytes()).hexdigest()
    assert digest==receipt['sha256']
    with h5py.File(p) as f: a=f['Data/Table Layout'][:]
    b=a[(a['ut1_unix']<t0+12600)&(a['ut2_unix']>t0)]
    assert len(a)==receipt['table_rows']
    assert len(b)==receipt.get('context_rows',receipt.get('context_rows_utc_0230_0600'))
    products[k]=dict(sha256=digest,total=len(a),context=len(b))
    if k==6400: data=b
p=root/'MAD6302_2017-12-18_bella_60@vhf.part.hdf5'
assert hashlib.sha256(p.read_bytes()).hexdigest()==products[6302]['sha256']
a=data
mask=(a['gfit']==0)&(a['ne']>0)&(a['dne']/a['ne']<.5)&(a['chisq']<10)&(a['ti']>50)&((a['gdalt']>=95)|(a['ne']<1e12))
assert mask.sum()==7452
b=a[mask&(a['gdalt']>=80)&(a['gdalt']<200)]
assert len(b)==3087 and len(np.unique(b['recno']))==208
assert len(np.unique(b['azm']))==len(np.unique(b['elm']))==1
az,el=np.deg2rad([b['azm'][0],b['elm'][0]])
r=np.array([np.cos(el)*np.sin(az),np.cos(el)*np.cos(az),np.sin(el)])
# Orthogonal completion in station ENU: line-of-sight observer kernel.
p=np.array([np.cos(az),-np.sin(az),0]);q=np.cross(r,p)
F=np.column_stack((r,p,q));assert np.allclose(F.T@F,np.eye(3))
v=b['vo'].astype(float);D=b['dvo'].astype(float)
base=v[:,None]*r;alt=base+100*p-50*q
assert np.max(np.abs(alt@r-v))<1e-10
assert np.max(np.abs(np.sum(alt**2,axis=1)-v*v-12500))<1e-9
# Exact abstract section and nullspace, valid in any orthonormal beam frame.
x,y,z=s.symbols('x y z',real=True);M=s.Matrix([[1,0,0]]);V=s.Matrix([x,y,z]);P=M.T*M
assert P*P==P and M*(s.eye(3)-P)==s.zeros(1,3)
assert s.expand(V.dot(V)-(M*V)[0]**2-y*y-z*z)==0
# Spectral-weight integral for one circular eigenvalue in cold Drude model.
w,om=s.symbols('w om',real=True);nu,d=s.symbols('nu d',positive=True)
A=d*s.atan((w-om)/nu)
assert s.simplify(s.diff(A,w)-d*nu/(nu**2+(w-om)**2))==0
assert s.limit(A,w,s.oo)-s.limit(A,w,-s.oo)==s.pi*d
assert s.simplify((s.limit(A,w,s.oo)-A.subs(w,0))+(s.limit(A,w,s.oo)-A.subs(w,0).subs(om,-om))-s.pi*d)==0
# e-density alone determines electron spectral weight (not local conductivity).
nne=b['ne'].astype(float);de=nne*e**2/me
# If reported molecular/oxygen fractions are adopted as fixed composition priors,
# singly charged molecular masses 28--32 u and O+ 16 u bound ion weight.
fm=b['pm'].astype(float);fo=b['po+'].astype(float);assert np.allclose(fm+fo,1,rtol=0,atol=4e-8)
ion_lo=nne*e**2/u*(fm/32+fo/16);ion_hi=nne*e**2/u*(fm/28+fo/16)
# The composition fractions have no independent error calibration here.
quant=lambda v:[float(x) for x in np.quantile(v,[0,.5,1])]
T=b['ut2_unix']-b['ut1_unix'];f=[.005,.05,3.915,7.83,7800.]
# Boxcar model only, not an assertion of the original GUISDAP filter.
box={str(k):dict(max_abs_sinc=float(np.max(np.abs(np.sinc(k*T)))),envelope=float(min(1,1/(np.pi*k*T.min())))) for k in f}
print(json.dumps(dict(status='ORIGINAL_RADAR_FIBRE_AND_CONDITIONAL_SPECTRAL_WEIGHT',products=products,quality_accepted=int(mask.sum()),region_rows=len(b),records=len(np.unique(b['recno'])),beam_ENU=r.tolist(),pointwise_rank=1,pointwise_nullity=2,independent_row_nullity=2*len(b),los_velocity_m_s=quant(v),los_error_reported_m_s=quant(D),beam_interval_s=quant(T),electron_D_S_m_s=quant(de),electron_positive_frequency_two_circular_weight_rad_s=quant(np.pi*de),electron_plasma_frequency_Hz=quant(np.sqrt(de/epsilon_0)/(2*np.pi)),ion_weight_fraction_under_reported_priors=[float(np.min(ion_lo/de)),float(np.max(ion_hi/de))],boxcar=box,physical_admission=False,scope='Pointwise LOS observation diagnostic, not proof of actual alternative PDE histories; no neutral wind subtraction, calibrated uncertainty, atmospheric model or ground flux. Cold Drude spectral sum only; no HF phase reconstruction. Reported composition priors not independent measurements.'),indent=2))
