"""Original-row temperature Jacobian; no assumed heating or natural field."""
import argparse, hashlib, json
from pathlib import Path
import numpy as np

PACKET='d771b81b3498e4cf9424325afe9e27f1c3f8125d0ba6c608c175cb62bd955fb6'
FREQ=(0.,3.915,-3.915,7.83,-7.83,7800.,-7800.)


def electron_rate(T,O,N2,O2):
    return 2.33e-17*N2*(1-1.21e-4*T)*T+1.82e-16*O2*(1+.036*np.sqrt(T))*np.sqrt(T)+8.9e-17*O*(1+5.7e-4*T)*np.sqrt(T)


def electron_derivative(T,O,N2,O2):
    return 2.33e-17*N2*(1-2*1.21e-4*T)+1.82e-16*O2*(.5/np.sqrt(T)+.036)+8.9e-17*O*(.5/np.sqrt(T)+.000855*np.sqrt(T))


def transfer(nu,gyro,D,J,f):
    return D[:,None,None]*np.linalg.inv((nu-2j*np.pi*f)[:,None,None]*np.eye(3)+gyro[:,None,None]*J)


def jacobian(nu,gyro,D,J,dnu,f,g):
    # f = natural frequency, g = temperature modulation frequency.
    A=(nu-2j*np.pi*(f+g))[:,None,None]*np.eye(3)+gyro[:,None,None]*J
    return -np.linalg.solve(A,dnu[:,None,None]*transfer(nu,gyro,D,J,f))


def self_test():
    import sympy as s
    T=s.symbols('T',positive=True); O,N2,O2=s.symbols('O N2 O2',nonnegative=True)
    a=s.Rational('2.33e-17')*N2*(1-s.Rational('1.21e-4')*T)*T+s.Rational('1.82e-16')*O2*(s.sqrt(T)+s.Rational('.036')*T)+s.Rational('8.9e-17')*O*(s.sqrt(T)+s.Rational('5.7e-4')*T**s.Rational(3,2))
    b=s.Rational('2.33e-17')*N2*(1-2*s.Rational('1.21e-4')*T)+s.Rational('1.82e-16')*O2*(1/(2*s.sqrt(T))+s.Rational('.036'))+s.Rational('8.9e-17')*O*(1/(2*s.sqrt(T))+s.Rational('.000855')*s.sqrt(T))
    assert s.simplify(s.diff(a,T)-b)==0
    T=np.array([200.,400.,800.]); O=np.array([1e15,2e15,3e15]); N2=O*2; O2=O/2
    nu=electron_rate(T,O,N2,O2); d=electron_derivative(T,O,N2,O2); gyro=np.array([-3.,-5.,-8.]); D=np.array([1.,2.,4.]); J=np.tile([[0.,-1.,0.],[1.,0.,0.],[0.,0.,0.]],(3,1,1))
    worst=0.
    for f in FREQ:
        for g in FREQ:
            v=jacobian(nu,gyro,D,J,d,f,g)
            assert np.allclose(v.conj(),jacobian(nu,gyro,D,J,d,-f,-g))
            if g==0:
                h=.001; ref=(transfer(electron_rate(T+h,O,N2,O2),gyro,D,J,f)-transfer(electron_rate(T-h,O,N2,O2),gyro,D,J,f))/(2*h)
                err=np.linalg.norm(v-ref)/max(np.linalg.norm(v),1e-30); worst=max(worst,float(err)); assert err<1e-7
    return dict(symbolic_derivative=True,signed_frequency_pairs=len(FREQ)**2,max_finite_difference_relative_error=worst,original_rows=0)


def replay(root,packet,output):
    from scipy.constants import elementary_charge as e,electron_mass as me,atomic_mass as u
    from solar_earth_model_inputs import radar
    from solar_earth_collision_tensor import rates,composition
    raw=packet.read_bytes(); assert hashlib.sha256(raw).hexdigest()==PACKET
    rows=radar(root); model=[json.loads(x) for x in raw.splitlines()]; assert len(rows)==len(model)==3087
    for r,m in zip(rows,model): assert all(r[key]==m[key] for key in ('record','range_km','utc'))
    B=np.array([m['B_NED_T'] for m in model]); mag=np.linalg.norm(B,axis=1); b=B/mag[:,None]; J=np.cross(b[:,None,:],np.eye(3)).swapaxes(1,2)
    mass=np.array([me,30.5*u,16*u]); q=e*np.array([-1,1,1]); pop=np.array([r['ne'] for r in rows])[:,None]*np.column_stack([np.ones(len(rows)),composition(root,rows)]); D=pop*q*q/mass; gyro=mag[:,None]*q/mass; T=np.array([r['te'] for r in rows]); result={}; worst=0.
    for label in ('history','daily'):
        neutral=np.array([m['neutral_'+label+'_SI'] for m in model]); nu=rates(rows,neutral); O,N2,O2=neutral[:,1],neutral[:,2],neutral[:,3]; d=electron_derivative(T,O,N2,O2)
        assert np.allclose(nu[:,0],electron_rate(T,O,N2,O2))
        for f in (0.,3.915,7.83,7800.):
            z=sum(transfer(nu[:,i],gyro[:,i],D[:,i],J,f) for i in range(3)); ref=np.array([m['tensor_by_history_and_frequency'][label][str(int(f) if f.is_integer() else f)] for m in model]); ref=ref[...,0]+1j*ref[...,1]
            err=float(np.max(np.linalg.norm(z-ref,axis=(1,2))/np.linalg.norm(ref,axis=(1,2)))); worst=max(worst,err); assert err<1e-10
        result[label]={(f,g):jacobian(nu[:,0],gyro[:,0],D[:,0],J,d,f,g) for f in FREQ for g in FREQ}
        for (f,g),v in result[label].items(): assert np.allclose(v.conj(),result[label][-f,-g])
    with output.open('x') as file:
        for i,r in enumerate(rows):
            item={key:r[key] for key in ('record','range_km','utc','height_km')}; item['temperature_response_S_m_K']={label:{f'{f},{g}':np.stack((v[i].real,v[i].imag),axis=-1).tolist() for (f,g),v in data.items()} for label,data in result.items()}; file.write(json.dumps(item,allow_nan=False)+'\n')
    return dict(original_rows=len(rows),source_packet_sha256=PACKET,output_sha256=hashlib.sha256(output.read_bytes()).hexdigest(),max_baseline_relative_error=worst,signed_frequency_pairs_per_row=2*len(FREQ)**2,physical_admission=False,scope='Per-kelvin electron collision perturbation, fixed population, ion temperature, magnetic and neutral geometry; no heating amplitude, chemical evolution, measured natural E, spatial adjacency or power attribution inferred.')


if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--root',type=Path); p.add_argument('--packet',type=Path); p.add_argument('--output',type=Path); a=p.parse_args(); out={'self_test':self_test()}
    if any((a.root,a.packet,a.output)):
        if not all((a.root,a.packet,a.output)): p.error('all three original replay arguments required')
        out['replay']=replay(a.root,a.packet,a.output)
    print(json.dumps(out,indent=2))
