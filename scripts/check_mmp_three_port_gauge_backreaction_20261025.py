#!/usr/bin/env python3
"""Three independently timed source currents with finite U(1) backreaction.

Source roots: Hebenstreit, Berges & Gelfand (PRD 87,105006,2013);
Kasper, Hebenstreit & Berges (PRD 90,025016,2014). Same finite
18x18 two-component Wilson--Dirac ring as dashi_agda PR #1248's
check_mmp_three_independent_retarded_source_ports_20261025.py.

This is semiclassical 1+1 dimensional electrostatics in temporal gauge,
with externally prescribed classical conserved (charge,current) sources;
it has NO transverse radiative photon, 3+1D plasma fluid, geometric
Einstein stress, renormalized Hadamard state or traversable throat.
"""
import json
import numpy as np
from scipy.integrate import solve_ivp

N = 9
D = 2*N
G2 = .35
FINAL = 3.4
Z = np.diag([1.,-1.]).astype(complex)
X = np.array([[0,1],[1,0]],complex)
B = -.31*(.55*Z+1j*X)
MASS = .85+.095*np.cos(2*np.pi*np.arange(N)/N)+.06*np.sin(4*np.pi*np.arange(N)/N)
WINDOWS = ((.2,1.18),(1.04,2.12),(2.28,3.04))
PORTS = (1,4,7)

def hamiltonian(theta):
    h=np.zeros((D,D),dtype=complex)
    for j in range(N):
        k=(j+1)%N
        h[2*j:2*j+2,2*j:2*j+2] = MASS[j]*Z
        hop=np.exp(1j*theta[j])*B
        h[2*j:2*j+2,2*k:2*k+2]=hop
        h[2*k:2*k+2,2*j:2*j+2]=hop.conj().T
    return h

H0=hamiltonian(np.zeros(N))
eig,v=np.linalg.eigh(H0)
assert np.count_nonzero(eig<0)==N
P0=v[:,eig<0]@v[:,eig<0].conj().T

def density(p):
    return np.array([np.trace(p[2*j:2*j+2,2*j:2*j+2]).real for j in range(N)])
NEUTRALIZING_BACKGROUND=density(P0)

def current(h,p):
    return np.array([-2*np.imag(np.trace(h[2*j:2*j+2,2*((j+1)%N):2*((j+1)%N)+2]@
               p[2*((j+1)%N):2*((j+1)%N)+2,2*j:2*j+2])) for j in range(N)])

def external_current(t,amplitudes):
    x=np.zeros(N)
    for i,(a,b) in enumerate(WINDOWS):
        if a<t<b:
            x[PORTS[i]]=amplitudes[i]*np.sin(np.pi*(t-a)/(b-a))**4
    return x

def pack(p,theta,efield,qext,work):
    return np.r_[p.ravel(),theta.astype(complex),efield.astype(complex),qext.astype(complex),complex(work)]

def unpack(y):
    return y[:D*D].reshape((D,D)),y[D*D:D*D+N].real,y[D*D+N:D*D+2*N].real,y[D*D+2*N:D*D+3*N].real,y[-1].real

Y0=pack(P0,np.zeros(N),np.zeros(N),np.zeros(N),0.)

def rhs(t,y,amplitudes):
    p,theta,efield,qext,work=unpack(y)
    h=hamiltonian(theta)
    j=current(h,p)
    ext=external_current(t,amplitudes)
    return pack(-1j*(h@p-p@h),G2*efield,-j+ext,ext-np.roll(ext,1),G2*efield@ext)

def gauss_residual(p,efield,qext):
    return efield-np.roll(efield,1)-(density(p)-NEUTRALIZING_BACKGROUND)-qext

def local_continuity_residual(p,theta):
    h=hamiltonian(theta)
    dp=-1j*(h@p-p@h)
    return density(dp)+current(h,p)-np.roll(current(h,p),1)

def energy(p,theta,efield):
    return np.trace(p@hamiltonian(theta)).real+G2*.5*np.dot(efield,efield)

INITIAL_ENERGY=energy(P0,np.zeros(N),np.zeros(N))

def simulate(amplitudes, end=FINAL, rtol=1e-10, atol=1e-11, initial=Y0):
    s=solve_ivp(lambda t,y:rhs(t,y,amplitudes),(0,end),initial,
                method='DOP853',atol=atol,rtol=rtol,dense_output=True,
                max_step=.045)
    assert s.success,s.message
    return s

def report(sol,t):
    p,theta,efield,qext,work=unpack(sol.sol(t))
    h=hamiltonian(theta)
    return {
        'time':float(t),
        'max_gauss_residual':float(np.max(abs(gauss_residual(p,efield,qext)))),
        'charge_conservation_error':float(abs(np.trace(p-P0))),
        'source_charge_neutrality_error':float(abs(qext.sum())),
        'projector_error':float(np.linalg.norm(p@p-p)),
        'local_continuity_residual':float(np.max(abs(local_continuity_residual(p,theta)))),
        'energy_minus_initial_minus_work':float(energy(p,theta,efield)-INITIAL_ENERGY-work),
        'fermion_density_change':float(np.linalg.norm(density(p)-NEUTRALIZING_BACKGROUND)),
        'electric_norm':float(np.linalg.norm(efield)),
        'external_work':float(work),
        'energy_gain':float(energy(p,theta,efield)-INITIAL_ENERGY),
    }

def gauge_covariance():
    # Static local U(1) transformation. Edge orientation matches PR #1248.
    chi=.3*np.sin(2*np.pi*np.arange(N)/N)+.1*np.cos(4*np.pi*np.arange(N)/N)
    diag=np.repeat(np.exp(1j*chi),2)
    u=np.diag(diag)
    tprime=chi-np.roll(chi,-1)
    pprime=u@P0@u.conj().T
    assert np.linalg.norm(hamiltonian(tprime)-u@H0@u.conj().T)<1e-12
    assert np.linalg.norm(current(hamiltonian(tprime),pprime)-current(H0,P0))<1e-12
    return float(np.linalg.norm(hamiltonian(tprime)-u@H0@u.conj().T))

def main():
    amps=(.18,-.14,.11)
    s=simulate(amps)
    records=[report(s,t) for t in (1.7,2.6,FINAL)]
    for r in records:
        assert r['max_gauss_residual']<3e-8,r
        assert r['charge_conservation_error']<3e-8,r
        assert r['source_charge_neutrality_error']<3e-8,r
        assert r['projector_error']<3e-8,r
        assert r['local_continuity_residual']<1e-12,r
        assert abs(r['energy_minus_initial_minus_work'])<3e-8,r
    assert records[-1]['fermion_density_change']>1e-5
    assert records[-1]['electric_norm']>1e-5
    pf,tf,ef,qf,wf=unpack(s.y[:,-1])
    # Compare to the source-only electric field: integral sin^4 = 3/8.
    # Source-only DOES NOT obey coupled Gauss law once matter responds.
    ebare=np.zeros(N)
    for i,(a,b) in enumerate(WINDOWS):
        ebare[PORTS[i]]=amps[i]*(b-a)*3/8
    backreaction=float(np.linalg.norm(ef-ebare))
    assert backreaction>1e-4
    # A future independent source has exactly no effect before it begins.
    third=simulate((0,0,amps[2]),end=1.7)
    a,b,c,d,w=unpack(third.y[:,-1]);assert np.linalg.norm(a-P0)<1e-10
    assert np.linalg.norm(b)+np.linalg.norm(c)+np.linalg.norm(d)+abs(w)<1e-10
    # No source, no energy injection or spurious vacuum excitation.
    off=simulate((0,0,0))
    off_record=report(off,FINAL)
    assert off_record['fermion_density_change']<1e-9
    assert abs(off_record['energy_gain'])<1e-9
    # Increasing accuracy should retain the same charge/density response.
    loose=simulate(amps,rtol=2e-7,atol=2e-8)
    p_lo,*_=unpack(loose.y[:,-1]);p_hi,*_=unpack(s.y[:,-1])
    convergence=float(np.linalg.norm(density(p_lo)-density(p_hi)))
    assert convergence<3e-6,convergence
    print(json.dumps({'model':'dynamical temporal-gauge electric links + 18x18 Wilson--Dirac CAR projector',
       'sources':'three independent external conserved charge/current ports',
       'parameters':{'sites':N,'g2':G2,'end':FINAL,'amplitudes':amps},
       'time_slices':records,'undriven':off_record,
       'source_only_vs_coupled_electric_difference':backreaction,
       'future_source_control':{'time':1.7,'state_difference_norm':float(np.linalg.norm(a-P0))},
       'static_local_u1_gauge_residual':gauge_covariance(),
       'loose_vs_strict_density_difference':convergence},indent=2))
    print('PASS: coupled finite gauge/fermion backreaction, source charge, Gauss, Ward, gauge covariance, exact-work residual')
    print('NOT CLAIMED: self-consistent 3+1D Maxwell, physical plasma, 4D Hadamard/Einstein solution')
if __name__=='__main__':main()
