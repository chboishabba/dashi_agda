"""SI periodic Maxwell/material/spherical integration with explicit input contract.
No inferred measured source, geometry, thermal law, or actuator efficiency.
Odd temporal sample count retains DC without an artificial Nyquist mode.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
from scipy.constants import epsilon_0, mu_0, elementary_charge as e, electron_mass as me, atomic_mass as u
from scipy.linalg import solve
from scipy.optimize import brentq
from scipy.optimize import minimize
from solar_earth_model_inputs import radar
from solar_earth_collision_tensor import rates, composition
from solar_earth_coupled_cell import generator
from solar_periodic_radial_weld import layer, R, H, ya
from solar_original_thermal_replay import PACKET

def original(root, packet, keys, label):
    raw=packet.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=PACKET: raise ValueError('historical packet mismatch')
    rows=radar(root); model=[json.loads(s) for s in raw.splitlines()]
    assert len(rows)==len(model)==3087
    index={}
    for i,(r,m) in enumerate(zip(rows,model)):
        assert all(r[k]==m[k] for k in ('record','range_km','utc'))
        index[(r['record'],r['range_km'])]=i
    ids=[index[tuple(key)] for key in keys]
    if len(set(ids))!=len(ids): raise ValueError('duplicate material row')
    rr=[rows[i] for i in ids]; mm=[model[i] for i in ids]
    neutral=np.array([m['neutral_'+label+'_SI'] for m in mm])
    B=np.array([m['B_NED_T'] for m in mm]); mag=np.linalg.norm(B,axis=1)
    mass=np.array([me,30.5*u,16*u]); q=e*np.array([-1,1,1])
    pop=np.array([r['ne'] for r in rr])[:,None]*np.column_stack([np.ones(len(rr)),composition(root,rr)])
    return rr,neutral,pop*q*q/mass,mag[:,None]*q/mass,B/mag[:,None]

def thermal_si(p,dt,capacity,cooling):
    """Held absorbed power W, heat capacity J/K, cooling W/K."""
    p=np.asarray(p,float); capacity=np.asarray(capacity,float); cooling=np.asarray(cooling,float)
    if np.any(p<0) or np.any(capacity<=0) or np.any(cooling<=0): raise ValueError('thermal contract')
    a=np.exp(-dt*cooling/capacity); b=-np.expm1(-dt*cooling/capacity)/cooling
    x=np.zeros_like(capacity)
    for v in p: x=a*x+b*v
    x/=-np.expm1(-len(p)*dt*cooling/capacity)
    initial=x.copy(); hist=[x.copy()]; midpoint=[]; cool=0.
    ah=np.exp(-dt*cooling/(2*capacity)); bh=-np.expm1(-dt*cooling/(2*capacity))/cooling
    for v in p:
        midpoint.append(ah*x+bh*v); y=a*x+b*v
        cool+=float(np.sum(dt*v-capacity*(y-x))); x=y; hist.append(x.copy())
    assert np.allclose(initial,x,rtol=1e-10,atol=1e-10)
    return np.array(hist),np.array(midpoint),cool

def shell(f,yg,sigma,dc_y,dc_ground):
    # DC externally supplied from independent static boundary solution.
    if f==0: return np.asarray(dc_y,float),np.asarray(dc_ground,float)
    if f<0:
        y,g=shell(-f,yg,sigma,dc_y,dc_ground); return y.conj(),g.conj()
    y=[]; g=[]
    for typ in ('TE','TM'):
        M=np.eye(2,dtype=complex)
        for lo,hi,sg in ((R,R+H/2,0.),(R+H/2,R+H,sigma)):
            M=layer(f,lo,hi,sg,typ).y[:,-1].reshape(2,2)@M
        a,b=M@np.array([1.,-yg])
        y.extend([-ya*b/a]*3); g.extend([np.sqrt(ya*yg)/a]*3)
    return np.array(y),np.array(g)

def aperture(normals,areas,volumes,frames):
    """Power-conjugate l=1 projection, e=r E_t in metres*V/m.
    Areas are oriented spherical surface quadrature in m^2; frames map NED
    vectors to common Cartesian coordinates. No radar-row adjacency inferred.
    """
    n=np.asarray(normals,float); a=np.asarray(areas,float); v=np.asarray(volumes,float); F=np.asarray(frames,float)
    assert np.allclose(np.linalg.norm(n,axis=1),1) and np.all(a>0) and np.all(v>0)
    assert np.allclose(F@F.transpose(0,2,1),np.eye(3)) and np.allclose(np.linalg.det(F),1)
    out=np.zeros((6,3*len(a)))
    for i in range(len(a)):
        P=np.eye(3)-np.outer(n[i],n[i])
        B=np.sqrt(1.5)*np.column_stack((np.cross(n[i],np.eye(3)).T,P))
        # l=1 normalized solid-angle convention; sqrt(4*pi) converts to total W.
        out[:,3*i:3*i+3]=a[i]/((R+H)*np.sqrt(4*np.pi*epsilon_0*v[i]))*B.T@F[i]
    return out

def solve_model(material, cfg, heat, source, normals=None, areas=None):
    rr,neutral,D,gyro,b=material; n=len(rr); N=len(source)
    if N<3 or N%2!=1: raise ValueError('odd temporal grid required')
    period=float(cfg['period_s']); dt=period/N
    if period<=0: raise ValueError('period')
    vol=np.array(cfg['volumes_m3']); Cth=np.array(cfg['heat_capacity_J_K']); kth=np.array(cfg['cooling_W_K'])
    th,mid,cool=thermal_si(heat,dt,Cth,kth)
    load=np.asarray(cfg['load_S_m'],float); eta=float(cfg['heater_efficiency'])
    if not 0<eta<=1 or np.any(load<0): raise ValueError('load or efficiency')
    # Physical mesh supplied independently as an energy-normalized skew curl
    # operator on full state, including explicit magnetic degrees of freedom.
    # Existing local material generator is the owner of all species couplings.
    blocks=[]; slices=[]; offset=0
    for i in range(n):
        A,_,_=generator(D[i],np.ones(3),gyro[i],b[i],epsilon_0,load[i])
        slices.append(slice(offset,offset+len(A))); offset+=len(A)
    K=np.asarray(cfg['curl_s_inv'],float); d=len(K)
    assert K.shape==(d,d) and d>=offset and np.allclose(K+K.T,0,atol=1e-12)
    E=np.array([j for sl in slices for j in range(sl.start,sl.start+3)])
    C=np.zeros((6,d)); C[:,E]=aperture(cfg['normals'] if normals is None else normals,cfg['areas_m2'] if areas is None else areas,vol,cfg['ned_to_cartesian'])
    for t in range(N):
        tr=[dict(r,te=r['te']+mid[t,i]) for i,r in enumerate(rr)]
        nu=rates(tr,neutral); A=K.copy()
        for i,sl in enumerate(slices):
            a,_,_=generator(D[i],nu[i],gyro[i],b[i],epsilon_0,load[i]); A[sl,sl]+=a
        blocks.append(A)
    A=np.array(blocks)
    f=np.fft.fftfreq(N,dt); F=np.fft.fft(np.eye(N),axis=0)/np.sqrt(N)
    derivative=(F.conj().T@((2j*np.pi*f)[:,None]*F)).real
    Y,G=map(np.array,zip(*(shell(z,cfg['ground_admittance_normalized'],cfg['shell_sigma_S_m'],cfg['dc_admittance_S'],cfg['dc_ground_transfer_sqrt_S']) for z in f)))
    assert np.all(Y.real>=abs(G)**2-1e-10)
    # Natural port c maps energy-normalized state to sqrt(W).
    c=np.asarray(cfg['source_port_sqrt_inv_s'],float); assert c.shape==(d,)
    M=np.kron(derivative,np.eye(d))+np.kron(np.eye(N),np.outer(c,c))
    for i in range(N): M[i*d:(i+1)*d,i*d:(i+1)*d]-=A[i]
    for q in range(6):
        M+=np.kron((F.conj().T@(Y[:,q,None]*F)).real,np.outer(C[q],C[q]))
    inc=np.asarray(source,float); rhs=2*inc[:,None]*c
    x=solve(M,rhs.ravel()).reshape(N,d)
    sh=F@(x@C.T); incoming=dt*float(inc@inc); outgoing=dt*float(np.sum((x@c-inc)**2))
    material_loss=-dt*np.einsum('ti,tij,tj->',x,A,x)
    useful=dt*sum(load[i]/epsilon_0*np.sum(x[:,sl.start:sl.start+3]**2) for i,sl in enumerate(slices))
    shell_work=dt*np.sum(Y.real*abs(sh)**2); ground=dt*np.sum(abs(G*sh)**2)
    absorbed=dt*np.sum(heat); paid=absorbed/eta+float(cfg['auxiliary_J'])
    err=incoming-outgoing-material_loss-shell_work
    assert abs(err)<1e-7*max(incoming,1e-20) and abs(absorbed-cool)<1e-8*max(absorbed,1e-20)
    assert ground<=shell_work+1e-8*max(shell_work,1e-20)
    # Source budget is a universal upper bound for all equal-resource passive
    # apertures on this model, not a claim of attainment.
    return dict(net_J=float(useful+ground-paid),load_J=float(useful),ground_J=float(ground),collision_J=float(material_loss-useful),shell_other_J=float(shell_work-ground),incident_J=incoming,outgoing_J=outgoing,absorbed_J=float(absorbed),paid_J=float(paid),cooling_J=float(cool),balance_J=float(err),passive_upper_J=incoming,history=x,thermal=th,dc=sh[0].real)

def static_shell(radii, conductivity, ground_S):
    """DC l=1 electroquasistatic conduction through conducting layers.
    Potential V=u(r)Y_1m; current flux q=-sigma*r^2*u'.
    Insulating layers require a distinct open-circuit electrostatic chart.
    Returns normalized harmonic potential admittance and ground transfer.
    Not interchangeable with an inductive TE DC magnetic termination.
    """
    radii=np.asarray(radii,float); conductivity=np.asarray(conductivity,float)
    if len(radii)!=len(conductivity)+1 or np.any(np.diff(radii)<=0) or np.any(conductivity<=0) or ground_S<=0:
        raise ValueError('positive conducting layers and ground required')
    M=np.eye(2)
    for a,b,s in zip(radii[:-1],radii[1:],conductivity):
        def chart(r): return np.array([[r,r**-2],[-s*r*r,2*s/r]])
        M=chart(b)@np.linalg.solve(chart(a),M)
    v,q=M@np.array([1.,-ground_S])
    Y=-q/v; G=np.sqrt(ground_S)/v
    assert Y>=G*G-1e-10*max(Y,1.)
    return float(Y),float(G)

def reverse_activation(material,cfg,geo,target_J):
    """Feasible minimum along a declared amplitude ray, not global monotonicity.
    Bracket every sampled crossing; retain failed probes and signed residual."""
    source=np.asarray(cfg['incident_sqrt_W'],float); shape=np.asarray(cfg['heating_shape'],float)
    def run(a): return solve_model(material,cfg,a*shape,source,geo['normals'],geo['areas_m2'])
    amps=np.linspace(0,cfg['max_heating_W'],33)
    vals=[]
    for a in amps:
        v=run(a); vals.append(v['load_J']+v['ground_J']-target_J)
    feasible=[float(a) for a,v in zip(amps,vals) if v>=0]
    for i in range(len(amps)-1):
        if vals[i]*vals[i+1]<0:
            feasible.append(brentq(lambda a:run(a)['load_J']+run(a)['ground_J']-target_J,amps[i],amps[i+1]))
    if not feasible: return dict(status='NO_SAMPLED_WITNESS',amplitudes_W=amps.tolist(),signed_residual_J=vals)
    a=min(feasible); out=run(a)
    return dict(status='FEASIBLE_RAY_WITNESS',amplitude_W=a,paid_J=out['paid_J'],target_residual_J=out['load_J']+out['ground_J']-target_J,amplitudes_W=amps.tolist(),signed_residual_J=vals)

def compare(material,cfg):
    source=np.asarray(cfg['incident_sqrt_W'],float); N=len(source); n=len(material[0]); zero=np.zeros((N,n))
    # Explicit oriented surface samples for every aspect ratio, same resource area.
    rows=[]; best=-np.inf
    for name,geo in cfg['geometries'].items():
        areas=np.asarray(geo['areas_m2'],float)
        assert np.isclose(sum(areas),sum(cfg['areas_m2']),rtol=1e-10)
        normals=geo['normals']; shape=np.asarray(cfg['heating_shape'],float)
        assert shape.shape==zero.shape and np.all(shape>=0)
        def run(a,s): return solve_model(material,cfg,a*shape,s,normals,areas)
        base=run(0.,source); best=max(best,base['net_J'])
        result=minimize(lambda a:-run(a[0],source)['net_J'],[0.],bounds=[(0.,cfg['max_heating_W'])],method='L-BFGS-B')
        active=run(float(result.x[0]),source); off=run(float(result.x[0]),source*0)
        trim=lambda a:{k:v for k,v in a.items() if not isinstance(v,np.ndarray)}
        rows.append(dict(geometry=name,amplitude_W=float(result.x[0]),optimizer_success=bool(result.success),passive=trim(base),active=trim(active),source_off=trim(off)))
    inverse={name:reverse_activation(material,cfg,geo,cfg['target_useful_J']) for name,geo in cfg['geometries'].items()} if 'target_useful_J' in cfg else {}
    return dict(rows=rows,inverse=inverse,best_tested_passive_J=best,unrestricted_passive_upper_J=rows[0]['passive']['incident_J'],physical_admission=False,scope='Explicit input geometry, fixed populations, SI periodic Galerkin model; independently supplied static port and skew curl; no measured actuator, source or global optimum inferred.')

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('root',type=Path); p.add_argument('packet',type=Path); p.add_argument('config',type=Path); a=p.parse_args()
    cfg=json.loads(a.config.read_text()); m=original(a.root,a.packet,cfg['row_keys'],cfg['history']); print(json.dumps(compare(m,cfg),indent=2))
