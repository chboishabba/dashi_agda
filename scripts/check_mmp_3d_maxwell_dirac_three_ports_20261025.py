#!/usr/bin/env python3
"""3+1D finite *semiclassical* Wilson-Dirac + compact U(1) spatial Maxwell test.

27 sites (3x3x3), four-component spinors, 81 gauge links, 81 spatial
plaquettes, three independent externally prescribed U(1) source ports.
Single occupied negative-energy four-spinor orbitals evolve unitarily;
classical links backreact via SAME fermion energy and plaquette action.

Repo predecessors: CompactLieLatticeGauge; MaxwellFiniteExteriorChainStrengthening;
YangMillsLatticeStressWardSliceConservationExact; MMP 2D coupled
finite gauge-field checker (dashi_agda #1248).
Original lattice gauge / real-time fermion science: Wilson (1974),
Hebenstreit/Berges/Gelfand (2013), Kasper/Hebenstreit/Berges (2014).
No 4D covariant/Hadamard renormalization, dynamical MHD, Einstein metric,
quantized photon Hilbert space or traversable wormhole is represented.
"""
from __future__ import annotations
import json
import numpy as np
from functools import lru_cache

L=3
S=L**3
ECOUNT=3*S
FCOUNT=3*S
SPIN=4
DIM=SPIN*S
G2=.35
R=.42
FINISH=3.4
PORTS=((1,0,0,0),(0,1,1,1),(2,2,2,2))
WINDOWS=((.2,1.18),(1.04,2.12),(2.28,3.04))
AMPS=(.18,-.14,.11)
pauli=(np.array([[0,1],[1,0]],complex),
       np.array([[0,-1j],[1j,0]],complex),
       np.diag([1.,-1.]).astype(complex))
I2=np.eye(2,dtype=complex)
beta=np.kron(pauli[2],I2)
alpha=tuple(np.kron(pauli[0],s) for s in pauli)
assert all(np.linalg.norm(a@a-np.eye(SPIN))<1e-12 for a in alpha)
assert all(np.linalg.norm(a@beta+beta@a)<1e-12 for a in alpha)
assert all(np.linalg.norm(alpha[i]@alpha[j]+alpha[j]@alpha[i])<1e-12
           for i in range(3) for j in range(i+1,3))
B=tuple(-.5*(R*beta+1j*alpha[d]) for d in range(3))

def site(x,y,z): return (x%L*L+y%L)*L+z%L
def edge(x,y,z,d):return 3*site(x,y,z)+d
def shift(x,y,z,d):
    arr=[x,y,z];arr[d]+=1
    return tuple(arr)
coords=[(x,y,z) for x in range(L) for y in range(L) for z in range(L)]
endpoints=[]
D=np.zeros((S,ECOUNT),int)
C=np.zeros((FCOUNT,ECOUNT),int)
for x,y,z in coords:
    i=site(x,y,z)
    for d in range(3):
        ex=edge(x,y,z,d)
        j=site(*shift(x,y,z,d))
        endpoints.append((i,j,d))
        D[i,ex]+=1;D[j,ex]-=1
    for plane,(a,b) in enumerate(((0,1),(1,2),(2,0))):
        face=3*i+plane
        C[face,edge(x,y,z,a)]+=1
        C[face,edge(*shift(x,y,z,a),b)]+=1
        C[face,edge(*shift(x,y,z,b),a)]-=1
        C[face,edge(x,y,z,b)]-=1
assert len(endpoints)==ECOUNT
assert np.array_equal(D@C.T,np.zeros((S,FCOUNT),int))
assert np.array_equal(C@D.T,np.zeros((FCOUNT,S),int))
assert np.linalg.matrix_rank(D)==S-1
assert np.linalg.matrix_rank(C)==2*S-2
ON_SITE=np.stack([(.88+3*R+.065*np.sin(2*np.pi*x/L)
                  +.035*np.cos(2*np.pi*y/L)+.02*np.sin(2*np.pi*z/L))*beta
                  for x,y,z in coords])

def hamiltonian(theta):
    h=np.zeros((DIM,DIM),complex)
    for s in range(S):h[SPIN*s:SPIN*s+SPIN,SPIN*s:SPIN*s+SPIN]=ON_SITE[s]
    for a,(j,k,d) in enumerate(endpoints):
        hop=np.exp(1j*theta[a])*B[d]
        h[SPIN*j:SPIN*j+SPIN,SPIN*k:SPIN*k+SPIN]+=hop
        h[SPIN*k:SPIN*k+SPIN,SPIN*j:SPIN*j+SPIN]+=hop.conj().T
    return h
H0=hamiltonian(np.zeros(ECOUNT))
assert np.linalg.norm(H0-H0.conj().T)<1e-12
spectrum,vectors=np.linalg.eigh(H0)
assert np.count_nonzero(spectrum<0)==DIM//2
V0=vectors[:,:DIM//2].copy()
INITIAL_GAP=float(spectrum[DIM//2]-spectrum[DIM//2-1])

def densities(V):
    return np.array([np.vdot(V[SPIN*s:SPIN*s+SPIN],V[SPIN*s:SPIN*s+SPIN]).real
                    for s in range(S)])
N_BACKGROUND=densities(V0)

def fermion_energy_and_current(V,theta,return_hv=False):
    # Hamiltonian-vector product in O(number-of-links * four-spinor * occupancy)
    # rather than dense O(DIM^3) evolution of a full CAR projector.
    hv=np.einsum('sab,sbc->sac',ON_SITE,V.reshape(S,SPIN,-1)).reshape(DIM,-1)
    current=np.zeros(ECOUNT)
    for a,(s,k,d) in enumerate(endpoints):
        us=V[SPIN*s:SPIN*s+SPIN]
        uk=V[SPIN*k:SPIN*k+SPIN]
        hop=np.exp(1j*theta[a])*B[d]
        hok=hop@uk
        hv[SPIN*s:SPIN*s+SPIN]+=hok
        hv[SPIN*k:SPIN*k+SPIN]+=hop.conj().T@us
        current[a]=-2*np.imag(np.vdot(us,hok))
    energy=float(np.vdot(V,hv).real)
    return (energy,current,hv) if return_hv else (energy,current)


def source(t,amplitudes):
    current=np.zeros(ECOUNT)
    for i,((x,y,z,d),(a,b)) in enumerate(zip(PORTS,WINDOWS)):
        if a<t<b:
            current[edge(x,y,z,d)]=amplitudes[i]*np.sin(np.pi*(t-a)/(b-a))**4
    return current


def field_energy(theta,e):
    return G2*.5*float(np.dot(e,e))+float(np.sum(1-np.cos(C@theta)))/G2

def energy(V,theta,e):
    return fermion_energy_and_current(V,theta)[0]+field_energy(theta,e)
E0=energy(V0,np.zeros(ECOUNT),np.zeros(ECOUNT))

# y = [occupied 108x54 orbital matrix, 81 theta, 81 E, 27 ext charge, 1 work].
BLOCK=DIM*(DIM//2)
def pack(V,theta,e,q,work):
    return np.r_[V.ravel(),np.asarray(theta,dtype=complex),
                  np.asarray(e,dtype=complex),np.asarray(q,dtype=complex),complex(work)]
def unpack(y):
    return (y[:BLOCK].reshape(DIM,DIM//2),y[BLOCK:BLOCK+ECOUNT].real,
            y[BLOCK+ECOUNT:BLOCK+2*ECOUNT].real,
            y[BLOCK+2*ECOUNT:BLOCK+2*ECOUNT+S].real,float(y[-1].real))
Y0=pack(V0,np.zeros(ECOUNT),np.zeros(ECOUNT),np.zeros(S),0.)

def rhs(t,y,amps,with_fermion=True,with_magnetic=True):
    V,theta,e,q,_=unpack(y)
    _,j,hv=fermion_energy_and_current(V,theta,True)
    i=source(t,amps)
    magnetic=C.T@np.sin(C@theta)/G2 if with_magnetic else 0.
    return pack(-1j*hv,G2*e,-j*int(with_fermion)-magnetic+i,D@i,G2*np.dot(e,i))

def integrate(amps=AMPS,finish=FINISH,dt=.04,with_fermion=True,with_magnetic=True,
              initial=None):
    # Fixed RK4; use grid alignment with pulse endpoints only through f(t)
    times=np.linspace(0,finish,int(np.ceil(finish/dt))+1)
    y=Y0.copy() if initial is None else initial.copy()
    for a,b in zip(times[:-1],times[1:]):
        h=b-a
        k1=rhs(a,y,amps,with_fermion,with_magnetic)
        k2=rhs(a+h/2,y+h*k1/2,amps,with_fermion,with_magnetic)
        k3=rhs(a+h/2,y+h*k2/2,amps,with_fermion,with_magnetic)
        k4=rhs(b,y+h*k3,amps,with_fermion,with_magnetic)
        y+=(h/6)*(k1+2*k2+2*k3+k4)
    return y

def report(y):
    V,theta,e,q,work=unpack(y)
    _,j,hv=fermion_energy_and_current(V,theta,True)
    dn=2*np.real(np.einsum('sao,sao->s',V.reshape(S,SPIN,-1).conj(),
                                   (-1j*hv).reshape(S,SPIN,-1)))
    b=C@theta
    return {
      'max_gauss_error':float(np.max(abs(D@e-(densities(V)-N_BACKGROUND)-q))),
      'max_local_fermion_ward':float(np.max(abs(dn+D@j))),
      'total_fermion_charge_error':float(abs(np.vdot(V,V)-DIM//2)),
      'external_total_charge_error':float(abs(q.sum())),
      'car_orthonormal_error':float(np.linalg.norm(V.conj().T@V-np.eye(DIM//2))),
      'energy_work_residual':float(energy(V,theta,e)-E0-work),
      'field_electric_energy':float(G2/2*e@e),
      'magnetic_field_energy':float(np.sum(1-np.cos(b))/G2),
      'magnetic_flux_norm':float(np.linalg.norm(b)),
      'curl_magnetic_force_norm':float(np.linalg.norm(C.T@np.sin(b)/G2)),
      'electric_norm':float(np.linalg.norm(e)),
      'matter_density_change':float(np.linalg.norm(densities(V)-N_BACKGROUND)),
      'input_work':work,
      'total_energy_gain':float(energy(V,theta,e)-E0),
      'total_oriented_face_flux':float(np.sum(b)),
    }


def check_hodge():
    eig=np.linalg.eigvalsh(D.T@D+C.T@C)
    # The 3 harmonic modes reflect H^1(T^3;R)=R^3.
    near_zero=int(np.count_nonzero(abs(eig)<1e-10))
    assert near_zero==3
    nonzero=np.rint(eig[eig>1e-10]).astype(int)
    assert set(nonzero.tolist())=={3,6,9}
    assert max(abs(eig[eig>1e-10]-nonzero))<1e-10
    # Of 81 links, 26 longitudinal, 52 coexact, 3 harmonic.
    assert np.linalg.matrix_rank(D)==26 and np.linalg.matrix_rank(C)==52
    return {'rank_d':26,'rank_c':52,'harmonic_one_form_dimension':near_zero,
            'free_maxwell_lattice_laplacian_nonzero_spectrum':{
              str(k):int(np.count_nonzero(nonzero==k)) for k in (3,6,9)},
            'curl_grad_norm':float(np.linalg.norm(C@D.T)),
            'div_curl_norm':float(np.linalg.norm(D@C.T))}

def check_gauge():
    phi=np.array([.19*np.sin(2*np.pi*x/L)+.12*np.cos(2*np.pi*y/L)
                  +.06*np.sin(2*np.pi*z/L) for x,y,z in coords])
    angle=D.T@phi
    g=np.repeat(np.exp(1j*phi),SPIN)[:,None]
    ve=g*V0
    eq1=np.linalg.norm(hamiltonian(angle)-
        np.diag(g.ravel())@H0@np.diag(g.ravel().conj()))
    assert eq1<1e-12
    assert np.linalg.norm(C@angle)<1e-12
    # This also tests the *driven* system, not only static conjugacy.
    first=integrate(dt=.012)
    twisted=integrate(dt=.012,initial=pack(ve,angle,np.zeros(ECOUNT),np.zeros(S),0.))
    V,t,e,q,w=unpack(first);Vt,tt,et,qt,wt=unpack(twisted)
    cov={'static_hamiltonian_error':float(eq1),
         'driven_density_matrix_error':float(np.linalg.norm(Vt@Vt.conj().T-
                   (g*V)@(g*V).conj().T)),
         'driven_link_angle_error':float(np.linalg.norm(tt-t-angle)),
         'driven_electric_error':float(np.linalg.norm(et-e)),
         'driven_external_charge_error':float(np.linalg.norm(qt-q)),
         'driven_plaquette_error':float(np.linalg.norm(C@(tt-t))),
         'driven_work_error':float(abs(wt-w))}
    assert max(cov.values())<5e-8,cov
    return cov

def main():
    hodge=check_hodge()
    coarse=integrate(dt=.008)
    fine=integrate(dt=.004)
    s=report(fine)
    print('Main fine:',json.dumps(s))
    assert s['max_gauss_error']<2e-9,s
    assert s['max_local_fermion_ward']<1e-10,s
    assert s['car_orthonormal_error']<2e-8,s
    assert abs(s['energy_work_residual'])<2e-8,s
    assert s['magnetic_field_energy']>1e-7 and s['matter_density_change']>1e-7
    density_change=float(np.linalg.norm(densities(unpack(fine)[0])-
                                        densities(unpack(coarse)[0])))
    assert density_change<5e-7,density_change
    negative_future=integrate((0.,0.,.11),finish=1.7,dt=.008)
    Vf,tf,ef,qf,wf=unpack(negative_future)
    future_dev=float(np.linalg.norm(Vf@Vf.conj().T-V0@V0.conj().T))
    assert future_dev<1e-7,future_dev
    assert np.linalg.norm(tf)+np.linalg.norm(ef)+np.linalg.norm(qf)+abs(wf)<1e-9
    # Confirm each of the two matter and magnetic feedback terms actually matters.
    no_magnetic=integrate(dt=.008,with_magnetic=False)
    no_matter=integrate(dt=.008,with_fermion=False)
    magnetic_ablation=float(np.linalg.norm(unpack(no_magnetic)[2]-unpack(coarse)[2]))
    broken_gauss=report(no_matter)['max_gauss_error']
    assert magnetic_ablation>1e-5 and broken_gauss>1e-5
    cov=check_gauge()
    data={'setting':'3+1D dimensional finite classical U1 Maxwell + four-spinor Wilson Dirac CAR, 27 sites',
          'hodge':hodge,'spectral_gap':INITIAL_GAP,
          'final_fine':s,'coarse_vs_fine_fermion_density_error':density_change,
          'future_source_no_response_error':future_dev,
          'magnetic_ablation_electric_difference':magnetic_ablation,
          'no_matter_feedback_gauss_error':broken_gauss,
          'driven_gauge_covariance':cov,
          'caveat':'Classical gauge links, source ports externally prescribed, flat periodic torus and no 4D renormalized CAR-Hadamard or Einstein/MHD solution.'}
    print(json.dumps(data,indent=2))
    print('PASS: 3 spatial dims, Clifford four-spinors, magnetic curls, 3 ports, local Ward/Gauss/energy, Hodge, ablations and dynamic gauge covariance')

if __name__=='__main__':main()
