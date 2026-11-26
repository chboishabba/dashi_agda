"""Replay original IGRF13 and MSIS00 sources; conditional local conductivity caps."""
import ctypes as C
import datetime as dt
import hashlib
import json
import math
import pathlib
import subprocess
import sys
import tempfile
import zipfile
import tarfile
import numpy as np
from scipy.special import lpmv, gammaln
from scipy.constants import elementary_charge as e, electron_mass as me, atomic_mass as u
from pyproj import Transformer
from solar_earth_model_inputs import radar, parse_gfz, forcing

D=C.c_double
class AP(C.Structure):
    _fields_=[('a',D*7)]
class Flags(C.Structure):
    _fields_=[('switches',C.c_int*24),('sw',D*24),('swc',D*24)]
class Input(C.Structure):
    _fields_=[('year',C.c_int),('doy',C.c_int)]+[(k,D) for k in ('sec','alt','lat','lon','lst','f107a','f107','ap')]+[('ap_a',C.POINTER(AP))]
class Output(C.Structure):
    _fields_=[('d',D*9),('t',D*2)]

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def run(*args): subprocess.run(args,check=True,capture_output=True)
def msis(lib,r,t,a,history):
    sec=(t-t.replace(hour=0,minute=0,second=0,microsecond=0)).total_seconds()
    ap=AP((D*7)(*a['ap_a'])); flags=Flags(); flags.switches[:]=[1]*24
    flags.switches[9]=-1 if history else 1
    i=Input(t.year,t.timetuple().tm_yday,sec,r['height_km'],r['lat'],r['lon'],(sec/3600+r['lon']/15)%24,a['f107a'],a['f107'],a['ap'],C.pointer(ap)); o=Output()
    lib.gtd7(C.byref(i),C.byref(flags),C.byref(o))
    return np.array([*o.d,*o.t])

def reference(lib,year,r):
    a=[C.c_int(0),D(year),C.c_int(1),D(r['height_km']),D(90-r['lat']),D(r['lon']),D(),D(),D(),D()]
    lib.igrf13syn_(*(C.byref(x) for x in a))
    return [x.value for x in a[-4:]]

def harmonics(root,rows,years):
    tr=Transformer.from_crs(4979,4978,always_xy=True)
    la=np.radians([r['lat'] for r in rows]); lo=np.radians([r['lon'] for r in rows])
    xyz=np.array(tr.transform([r['lon'] for r in rows],[r['lat'] for r in rows],[1000*r['height_km'] for r in rows]))/1000
    radius=np.linalg.norm(xyz,axis=0); gc=np.arcsin(xyz[2]/radius); x=np.sin(gc); st=np.cos(gc)
    g={}; h={}
    for line in (root/'igrf13coeffs.txt').read_text().splitlines():
        p=line.split()
        if p and p[0] in ('g','h'):
            n,m=map(int,p[1:3]); v=np.array(list(map(float,p[3:])))
            (g if p[0]=='g' else h)[n,m]=v[23]+(years-2015)/5*(v[24]-v[23])
    assert len(g)==104 and len(h)==91
    north=np.zeros(len(rows)); east=north.copy(); down=north.copy()
    for (n,m),gv in g.items():
        hv=h.get((n,m),0); fac=(-1)**m*np.exp((gammaln(n-m+1)-gammaln(n+m+1))/2)*np.sqrt(2 if m else 1)
        p=lpmv(m,n,x)*fac; prev=lpmv(m,n-1,x)*fac if n>m else 0
        dp=(n*x*p-(n+m)*prev)/st; co=np.cos(m*lo); si=np.sin(m*lo); scale=(6371.2/radius)**(n+2)
        v=scale*(gv*co+hv*si); north+=v*dp; down-=(n+1)*v*p; east+=scale*m*(gv*si-hv*co)*p/st
    delta=la-gc
    return np.array([north*np.cos(delta)+down*np.sin(delta),east,down*np.cos(delta)-north*np.sin(delta)]).T

def main(root):
    manifest=json.loads((root/'source_manifest.json').read_text()); hashes={x['local_file']:digest(root/x['local_file']) for x in manifest['sources']}
    assert all(hashes[x['local_file']]==x['sha256'] for x in manifest['sources']) and len(hashes)==9
    rows=radar(root); gfz=parse_gfz((root/'Kp_ap_Ap_SN_F107_since_1932.txt').read_text().splitlines()); times=[dt.datetime.fromisoformat(r['utc']) for r in rows]; a=[forcing(gfz,t) for t in times]
    years=np.array([t.year+(t-dt.datetime(t.year,1,1,tzinfo=t.tzinfo)).total_seconds()/(dt.datetime(t.year+1,1,1,tzinfo=t.tzinfo)-dt.datetime(t.year,1,1,tzinfo=t.tzinfo)).total_seconds() for t in times])
    with tempfile.TemporaryDirectory() as tmp:
        p=pathlib.Path(tmp); src=(root/'igrf13.f').read_text(); start=src.lower().index('      subroutine igrf13syn ('); (p/'syn.f').write_text(src[start:]); run('gfortran','-shared','-fPIC','-std=legacy','-O2',str(p/'syn.f'),'-o',str(p/'igrf.so'))
        ref=C.CDLL(str(p/'igrf.so')); b=np.array([reference(ref,y,r) for y,r in zip(years,rows)])
        libs=[]
        for j,(archive,kind) in enumerate([('nrlmsise-00-cmake-master.zip','zip'),('nrlmsise00-0.1.2.tar.gz','tar')]):
            dest=p/str(j); dest.mkdir()
            # Extract only the three explicitly needed basename members.
            with (zipfile.ZipFile(root/archive) if kind=='zip' else tarfile.open(root/archive)) as ar:
                names=ar.namelist() if kind=='zip' else ar.getnames()
                for name in ('nrlmsise-00.c','nrlmsise-00_data.c','nrlmsise-00.h'):
                    matches=[x for x in names if x.endswith('/'+name)]; assert len(matches)==1
                    data=ar.read(matches[0]) if kind=='zip' else ar.extractfile(matches[0]).read(); (dest/name).write_bytes(data)
            so=dest/'msis.so'; run('gcc','-shared','-fPIC','-O2',str(dest/'nrlmsise-00.c'),str(dest/'nrlmsise-00_data.c'),'-lm','-o',str(so)); libs.append(C.CDLL(str(so)))
        storm=np.array([msis(libs[0],r,t,f,True) for r,t,f in zip(rows,times,a)]); daily=np.array([msis(libs[0],r,t,f,False) for r,t,f in zip(rows,times,a)]); other=np.array([msis(libs[1],r,t,f,True) for r,t,f in zip(rows,times,a)])
    h=harmonics(root,rows,years); err=np.max(np.abs(b[:,:3]-h)); assert err<1,err
    assert np.allclose(np.linalg.norm(b[:,:3],axis=1),b[:,3],rtol=1e-12)
    assert np.all(np.isfinite(storm)) and np.all(storm[:,:9]>=0) and np.all(storm[:,9:]>0)
    assert np.allclose(storm,other,rtol=1e-12,atol=0)
    mag=b[:,3]*1e-9; ne=np.array([r['ne'] for r in rows]); cap=e*ne/mag
    # Actual main-field values constrain detuning; ion masses are conditional species priors.
    frequencies=[0,3.915,7.83,7800]; masses=[me,16*u,28*u,32*u]; gyro=np.array([e*mag/m/(2*np.pi) for m in masses]); quant=lambda z:np.quantile(z,[0,.5,1],axis=0).tolist()
    out=dict(status='SOURCE_BACKED_MODEL_REPLAY_CONDITIONAL',source_hashes=hashes,rows=len(rows),records=len(set(r['utc'] for r in rows)),forcing_first=a[0],forcing_last=a[-1],igrf_NED_nT=quant(b[:,:3]),igrf_magnitude_nT=quant(b[:,3]),harmonic_max_component_error_nT=float(err),msis_order=['He','O','N2','O2','Ar','rho','H','N','anomalous_O','Texo','Tlocal'],msis_storm_SI=quant(storm),msis_daily_SI=quant(daily),msis_two_sources_max_absolute_difference=float(np.max(np.abs(storm-other))),max_daily_storm_relative_difference=float(np.max(np.abs(daily-storm)/np.maximum(storm,1e-100))),dc_quasineutral_transverse_cap_S_m=quant(cap),gyro_frequency_Hz_species_order=['electron','O+','28u+','32u+'],gyro_frequency_Hz=quant(gyro.T),frequencies_Hz=frequencies,min_absolute_detuning_Hz={str(f):np.min(np.abs(gyro-f),axis=1).tolist() for f in frequencies},physical_admission=False)
    print(json.dumps(out,indent=2))
if __name__=='__main__': main(pathlib.Path(sys.argv[1]))
