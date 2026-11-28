"""Independent original-row sensitivity audit; no actuator or measured field inference."""
import json, hashlib, sys
from pathlib import Path
import numpy as np
from scipy.constants import elementary_charge as e, electron_mass as me
from solar_earth_model_inputs import radar
from solar_original_thermal_replay import FREQ, electron_rate, electron_derivative, transfer, jacobian, PACKET

def audit(root,packet):
    raw=packet.read_bytes(); assert hashlib.sha256(raw).hexdigest()==PACKET
    rows=radar(root); data=[json.loads(x) for x in raw.splitlines()]; assert len(rows)==len(data)==3087
    for r,m in zip(rows,data): assert all(r[key]==m[key] for key in ('record','range_km','utc'))
    B=np.array([m['B_NED_T'] for m in data]); mag=np.linalg.norm(B,axis=1); b=B/mag[:,None]
    P=b[:,:,None]*b[:,None,:]; Q=np.eye(3)-P; J=np.cross(b[:,None,:],np.eye(3)).swapaxes(1,2)
    plus=(Q-1j*J)/2; minus=(Q+1j*J)/2
    T=np.array([r['te'] for r in rows]); D=np.array([r['ne'] for r in rows])*e*e/me; gyro=-e*mag/me
    def rel(a,b):
        return float(np.max(np.linalg.norm(a-b,axis=(1,2))/np.maximum(np.linalg.norm(b,axis=(1,2)),1e-300)))
    worst=0.; fd=0.; reality=0.; stats={}
    for label in ('history','daily'):
        neutral=np.array([m['neutral_'+label+'_SI'] for m in data]); O,N2,O2=neutral[:,1],neutral[:,2],neutral[:,3]
        nu=electron_rate(T,O,N2,O2); d=electron_derivative(T,O,N2,O2); h=T*1e-4
        stats[label]={}; count=0
        for f in FREQ:
            for g in FREQ:
                z=jacobian(nu,gyro,D,J,d,f,g); a=nu-2j*np.pi*f; c=nu-2j*np.pi*(f+g)
                v=-(D*d)[:,None,None]*(P/(a*c)[:,None,None]+plus/((a+1j*gyro)*(c+1j*gyro))[:,None,None]+minus/((a-1j*gyro)*(c-1j*gyro))[:,None,None])
                worst=max(worst,rel(z,v)); reality=max(reality,rel(z.conj(),jacobian(nu,gyro,D,J,d,-f,-g))); count+=len(rows)
                if g==0:
                    ref=(transfer(electron_rate(T+h,O,N2,O2),gyro,D,J,f)-transfer(electron_rate(T-h,O,N2,O2),gyro,D,J,f))/(2*h[:,None,None])
                    fd=max(fd,rel(z,ref))
                if f==0. and g in (0.,3.915,7.83,7800.):
                    stats[label][str(g)]=dict(norm_quantiles=np.quantile(np.linalg.norm(z,axis=(1,2)),[0,.5,1]).tolist())
        stats[label]['checks']=count
        dp=D*d*(gyro**2-nu**2)/(nu**2+gyro**2)**2
        stats[label]['dc_pedersen_derivative_sign_counts']={'positive':int((dp>0).sum()),'negative':int((dp<0).sum()),'zero':int((dp==0).sum())}
    assert worst<1e-9 and reality<1e-12 and fd<1e-5
    return dict(rows=len(rows),signed_pair_evaluations=2*len(FREQ)**2*len(rows),dc_modulation_finite_differences=2*len(FREQ)*len(rows),max_circular_relative_error=worst,max_conjugacy_relative_error=reality,max_finite_difference_relative_error=fd,statistics=stats,physical_admission=False)

if __name__=='__main__': print(json.dumps(audit(Path(sys.argv[1]),Path(sys.argv[2])),indent=2))
