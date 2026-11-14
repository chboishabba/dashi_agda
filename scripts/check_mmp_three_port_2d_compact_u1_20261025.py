#!/usr/bin/env python3
"""Finite 2+1D Hamiltonian U(1) magnetic plaquette + Wilson-Dirac backreaction.

Three independent prescribed source-current ports, including source charge
continuity. Reuses dashi_agda #1248's finite CAR/projector model, with the
native CompactLieLatticeGauge path/plaquette, MaxwellFiniteExteriorChain,
and YangMillsLatticeStressWard finite algebra as distinct original owners.

Physical roots: Hebenstreit--Berges--Gelfand 2013 (1+1D); Kasper--
Hebenstreit--Berges 2014 (lattice quantum fermions/classical gauge fields).
This model has *two spatial dimensions*, prescribed external sources, and
classical electric/magnetic U(1) fields. It is not a solved 3+1D Maxwell-MHD,
curved Hadamard fermionic state, Einstein equation or physical MMP wormhole.
"""
from __future__ import annotations
import json
import numpy as np
from scipy.integrate import solve_ivp

L = 3
S = L*L
N = 2*S
ECOUNT = 2*S
G2 = .35
T = 3.4
I2 = np.eye(2, dtype=complex)
Z = np.diag([1.,-1.]).astype(complex)
X = np.array([[0.,1.],[1.,0.]],complex)
Y = np.array([[0.,-1j],[1j,0.]],complex)
B = [-.23*(.6*Z+1j*X),-.21*(.6*Z+1j*Y)]
PORTS = ((1,0,0),(0,1,1),(2,2,0))
WINDOWS = ((.2,1.18),(1.04,2.12),(2.28,3.04))
AMPLITUDES = (.18,-.14,.11)


def site(x,y):
    return (x%L)*L+(y%L)


def target(x,y,d):
    return site(x+(d==0),y+(d==1))


def edge(x,y,d):
    return 2*site(x,y)+d

# The 1-cochain differential C sends oriented link angles to oriented
# plaquette flux. The 0-cochain divergence D sends link currents to sites.
D = np.zeros((S,ECOUNT))
C = np.zeros((S,ECOUNT))
endpoints=[]
for x in range(L):
    for y in range(L):
        s=site(x,y)
        for d in range(2):
            k=target(x,y,d)
            a=edge(x,y,d)
            endpoints.append((s,k,d))
            D[s,a]+=1
            D[k,a]-=1
        C[s,edge(x,y,0)]+=1
        C[s,edge(x+1,y,1)]+=1
        C[s,edge(x,y+1,0)]-=1
        C[s,edge(x,y,1)]-=1
assert np.linalg.norm(D@C.T)==0  # boundary-of-boundary = 0
assert np.linalg.norm(C@D.T)==0  # pure site gauge gradient has no flux
assert all(endpoints[edge(x,y,d)][:2] == (site(x,y),target(x,y,d))
           for x in range(L) for y in range(L) for d in range(2))


def ham(theta):
    h=np.zeros((N,N),complex)
    for x in range(L):
        for y in range(L):
            j=site(x,y)
            mass=.98+.055*np.sin(2*np.pi*x/L)+.04*np.cos(2*np.pi*y/L)
            h[2*j:2*j+2,2*j:2*j+2]=mass*Z
    for a,(j,k,d) in enumerate(endpoints):
        h[2*j:2*j+2,2*k:2*k+2]=np.exp(1j*theta[a])*B[d]
        h[2*k:2*k+2,2*j:2*j+2]=(
            np.exp(1j*theta[a])*B[d]).conj().T
    return h


H0=ham(np.zeros(ECOUNT))
eig,v=np.linalg.eigh(H0)
assert sum(eig<0)==S and eig[S]>0
P0=v[:,eig<0]@v[:,eig<0].conj().T


def local_density(p):
    return np.array([np.trace(p[2*j:2*j+2,2*j:2*j+2]).real
                     for j in range(S)])


N_BACKGROUND=local_density(P0)


def links_current(h,p):
    j=np.zeros(ECOUNT)
    for a,(s,k,d) in enumerate(endpoints):
        j[a]=-2*np.imag(np.trace(h[2*s:2*s+2,2*k:2*k+2]@
                                   p[2*k:2*k+2,2*s:2*s+2]))
    return j


def external(t,amp):
    current=np.zeros(ECOUNT)
    for n,((x,y,d),(a,b)) in enumerate(zip(PORTS,WINDOWS)):
        if a<t<b:
            current[edge(x,y,d)]=amp[n]*np.sin(np.pi*(t-a)/(b-a))**4
    return current


def field_energy(theta,e):
    return .5*G2*(e@e)+sum(1-np.cos(C@theta))/G2


def total_energy(p,theta,e):
    return float((np.trace(p@ham(theta)).real+field_energy(theta,e)))


E0=total_energy(P0,np.zeros(ECOUNT),np.zeros(ECOUNT))


def pack(p,theta,e,qext,work):
    return np.r_[p.reshape(-1),np.asarray(theta,dtype=complex),
                 np.asarray(e,dtype=complex),np.asarray(qext,dtype=complex),
                 complex(work)]


def unpack(y):
    return (y[:N*N].reshape(N,N),y[N*N:N*N+ECOUNT].real,
            y[N*N+ECOUNT:N*N+2*ECOUNT].real,
            y[N*N+2*ECOUNT:N*N+2*ECOUNT+S].real,
            float(y[-1].real))


Y0=pack(P0,np.zeros(ECOUNT),np.zeros(ECOUNT),np.zeros(S),0.)


def rhs(t,y,amp,magnetic=True,matter=True):
    p,theta,efield,qext,_=unpack(y)
    h=ham(theta)
    j=links_current(h,p) if matter else np.zeros(ECOUNT)
    # Magnetic force comes from the same compact Wilson-plaquette energy.
    force=(C.T@np.sin(C@theta))/G2 if magnetic else np.zeros(ECOUNT)
    i=external(t,amp)
    dp=-1j*(h@p-p@h)
    return pack(dp,G2*efield,-j-force+i,D@i,G2*efield@i)


def evolve(amp=AMPLITUDES,t=T,magnetic=True,matter=True,
           rtol=1e-10,atol=1e-11):
    s=solve_ivp(lambda t,y:rhs(t,y,amp,magnetic,matter),(0,t),Y0,
                method='DOP853',max_step=.05,rtol=rtol,atol=atol,
                dense_output=True)
    assert s.success,s.message
    return s


def snapshot(y):
    p,theta,e,qext,work=unpack(y)
    h=ham(theta)
    jd=links_current(h,p)
    continuity=local_density(-1j*(h@p-p@h))+D@jd
    bflux=C@theta
    return {
        'gauss_max':float(np.max(np.abs(D@e-(local_density(p)-N_BACKGROUND)-qext))),
        'local_fermion_continuity_max':float(np.max(abs(continuity))),
        'total_fermion_charge_err':float(abs(np.trace(p-P0))),
        'total_external_charge_err':float(abs(sum(qext))),
        'projector_err':float(np.linalg.norm(p@p-p)),
        'energy_minus_initial_minus_work':float(total_energy(p,theta,e)-E0-work),
        'input_work':float(work),
        'energy_gain':float(total_energy(p,theta,e)-E0),
        'electric_norm':float(np.linalg.norm(e)),
        'magnetic_plaquette_flux_norm':float(np.linalg.norm(bflux)),
        'magnetic_field_energy':float(sum(1-np.cos(bflux))/G2),
        'net_plaquette_flux':float(sum(bflux)),
        'matter_density_change':float(np.linalg.norm(local_density(p)-N_BACKGROUND)),
        'force_magnetic_norm':float(np.linalg.norm(C.T@np.sin(bflux)/G2))}


def gauge_control():
    phi=np.array([.23*np.sin(2*np.pi*x/L)+.11*np.cos(2*np.pi*y/L)
                  for x in range(L) for y in range(L)])
    g=np.diag(np.repeat(np.exp(1j*phi),2))
    theta=D.T@phi
    p=g@P0@g.conj().T
    assert np.linalg.norm(ham(theta)-g@H0@g.conj().T)<1e-12
    assert np.linalg.norm(C@theta)<1e-12
    assert np.linalg.norm(links_current(ham(theta),p)-links_current(H0,P0))<1e-12
    return {'hamiltonian_covariance':float(np.linalg.norm(ham(theta)-g@H0@g.conj().T)),
            'plaquette_flux_pure_gauge':float(np.linalg.norm(C@theta))}


def negative_controls():
    baseline=evolve((0.,0.,0.))
    assert snapshot(baseline.y[:,-1])['matter_density_change']<1e-9
    future=evolve((0.,0.,.11),t=1.7)
    assert np.linalg.norm(future.y[:,-1]-Y0)<1e-8
    return {'no_drive_matter_density':snapshot(baseline.y[:,-1])['matter_density_change'],
            'future_port_before_activation_deviation':float(np.linalg.norm(future.y[:,-1]-Y0))}


def main():
    sol=evolve()
    rows={str(t):snapshot(sol.sol(t)) for t in (1.7,2.6,T)}
    for r in rows.values():
        assert r['gauss_max']<2e-8,r
        assert r['local_fermion_continuity_max']<1e-12,r
        assert r['total_fermion_charge_err']<2e-8,r
        assert r['total_external_charge_err']<2e-8,r
        assert r['projector_err']<2e-8,r
        assert abs(r['energy_minus_initial_minus_work'])<2e-8,r
        assert abs(r['net_plaquette_flux'])<1e-12,r
    full=rows[str(T)]
    assert full['matter_density_change']>1e-5
    assert full['magnetic_plaquette_flux_norm']>1e-5
    assert full['magnetic_field_energy']>0
    no_mag=evolve(magnetic=False)
    assert np.linalg.norm(unpack(no_mag.y[:,-1])[2]-unpack(sol.y[:,-1])[2])>1e-5
    no_feedback=evolve(matter=False)
    no_feedback_gauss=snapshot(no_feedback.y[:,-1])['gauss_max']
    assert no_feedback_gauss>1e-5
    weak=evolve(rtol=1e-7,atol=1e-8)
    convergence=float(np.linalg.norm(local_density(unpack(weak.y[:,-1])[0])-
                                     local_density(unpack(sol.y[:,-1])[0])))
    assert convergence<3e-6
    out={'model':'2+1D finite compact U1 Wilson plaquette + dynamical electric/magnetic fields and CAR fermions',
         'sites':S,'links':ECOUNT,'plaquettes':S,
         'mesh_chain':{'div_curl_residual':float(np.linalg.norm(D@C.T)),
                       'curl_grad_residual':float(np.linalg.norm(C@D.T))},
         'source_ports':PORTS,'time_windows':WINDOWS,'amplitudes':AMPLITUDES,
         'time_slices':rows,'static_gauge_control':gauge_control(),
         'negative_controls':negative_controls(),
         'no_magnetic_force_electric_difference':float(np.linalg.norm(
             unpack(no_mag.y[:,-1])[2]-unpack(sol.y[:,-1])[2])),
         'no_fermion_current_gauss_max':no_feedback_gauss,
         'weak_vs_strict_fermion_density_difference':convergence,
         'initial_spectral_gap':float(eig[S]-eig[S-1])}
    print(json.dumps(out,indent=2))
    print('PASS finite 2+1D magnetic plaquette U1/Dirac coupled conservation and controls')
    print('NOT a full 3+1D Maxwell-MHD, Hadamard/curved fermionic or Einstein solution')

if __name__=='__main__':
    main()
