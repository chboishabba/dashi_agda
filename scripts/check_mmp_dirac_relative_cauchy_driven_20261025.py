#!/usr/bin/env python3
"""Finite relative-Cauchy *analogue* for driven charged Wilson-Dirac states.

Original theory: Sanders 2009/2010, Zahn 2014/2015, Finster--Murro--Röken
2015. Native prior art: CompactLieLatticeGauge holonomyGaugeCovariant.
Finite matrices are NOT 4D Hadamard states, retarded curved spacetime
propagators, or Maxwell/Einstein/plasma solutions.
"""
import json
import numpy as np
from scipy.linalg import expm

N,T=9,3.
I=np.eye(2,dtype=complex)
Z=np.diag([1.,-1.]).astype(complex)
X=np.array([[0,1],[1,0]],complex)
B=-.31*(.55*Z+1j*X)
xs=np.arange(N)

def H(a=None,v=None):
    if a is None:a=np.zeros(N)
    if v is None:v=np.zeros(N)
    out=np.zeros((2*N,2*N),complex)
    for j in range(N):
        k=(j+1)%N
        out[2*j:2*j+2,2*j:2*j+2]=(
          .85+.095*np.cos(2*np.pi*j/N)+.06*np.sin(4*np.pi*j/N))*Z+v[j]*I
        hop=np.exp(1j*a[j])*B
        out[2*j:2*j+2,2*k:2*k+2]=hop
        out[2*k:2*k+2,2*j:2*j+2]=hop.conj().T
    assert np.linalg.norm(out-out.conj().T)<1e-12
    return out

H0=H()
energies,V0=np.linalg.eigh(H0)
P0=V0[:,energies<0]@V0[:,energies<0].conj().T
assert sum(energies<0)==N and energies[N]>0

def shape(amps):
    profiles=[]
    for center in (1,4,7):
        r=np.minimum(abs(xs-center),N-abs(xs-center))
        g=np.exp(-r*r/(2*.55**2))
        profiles.append(g/g.sum())
    return np.asarray(amps)@np.array(profiles)

def f(t):return np.sin(np.pi*t/T)**2
def fdot(t):return np.pi/T*np.sin(2*np.pi*t/T)
def chi(t):return .38*f(t)*(np.sin(2*np.pi*xs/N)+.21*np.cos(4*np.pi*xs/N))
def cdot(t):return .38*fdot(t)*(np.sin(2*np.pi*xs/N)+.21*np.cos(4*np.pi*xs/N))
def G(t):return np.diag(np.repeat(np.exp(1j*chi(t)),2))
def field(t,amp,s,gauge=False):
    a=amp*f(t)*s
    v=np.zeros(N)
    if gauge:
        a=a+chi(t)-np.roll(chi(t),-1)
        v=-cdot(t)
    return a,v

def evolve(amp,s,steps=180,gauge=False):
    dt=T/steps
    u=np.eye(2*N,dtype=complex)
    for k in range(steps):
        a,v=field((k+.5)*dt,amp,s,gauge)
        u=expm(-1j*H(a,v)*dt)@u
    return u

def P(u):return u@P0@u.conj().T
def source(s):
    out=np.zeros_like(H0)
    for j in range(N):
        k=(j+1)%N
        hop=1j*s[j]*B
        out[2*j:2*j+2,2*k:2*k+2]=hop
        out[2*k:2*k+2,2*j:2*j+2]=hop.conj().T
    return out

def linear(s,steps=180):
    C=source(s)@P0-P0@source(s)
    dt=T/steps
    out=np.zeros_like(H0)
    for k in range(steps):
        t=(k+.5)*dt
        u=expm(-1j*H0*(T-t))
        out+=(-1j*dt*f(t))*(u@C@u.conj().T)
    return out

def continuity(Pnow,Hnow):
    dn=np.array([np.trace((-1j*(Hnow@Pnow-Pnow@Hnow))
        [2*j:2*j+2,2*j:2*j+2]).real for j in range(N)])
    J=[]
    for j in range(N):
        k=(j+1)%N
        J.append(-2*np.imag(np.trace(Hnow[2*j:2*j+2,2*k:2*k+2]@
                                     Pnow[2*k:2*k+2,2*j:2*j+2])))
    J=np.array(J)
    return np.max(abs(dn+J-np.roll(J,1)))

def scenario(s,steps=180):
    u=evolve(.2,s,steps)
    ug=evolve(.2,s,steps,gauge=True)
    p=P(u)
    dt=.002
    derivative=(P(evolve(dt,s,steps))-P(evolve(-dt,s,steps)))/(2*dt)
    response=np.linalg.norm(derivative-linear(s,steps))
    ref=expm(-1j*H0*T)
    relative=ref.conj().T@u
    charge=float(np.trace(p-P0).real)
    energy=float(np.trace(H0@(p-P0)).real)
    assert abs(charge)<1e-10
    assert energy>=-1e-10
    assert np.linalg.norm(p@p-p)<1e-10
    assert abs(abs(np.linalg.det(relative))-1)<1e-9
    ward=continuity(p,H0)
    assert ward<1e-12
    return {'drive_wilson_angle_at_midpoint':float(.2*s.sum()),
       'relative_evolution_distance':float(np.linalg.norm(relative-np.eye(2*N))),
       'local_density_change':float(np.linalg.norm([
           np.trace((p-P0)[2*j:2*j+2,2*j:2*j+2]).real for j in range(N)])),
       'charge_change':charge,'ground_state_energy_gain':energy,
       'local_continuity_error':float(ward),
       'projector_idempotence_error':float(np.linalg.norm(p@p-p)),
       'time_dependent_gauge_error':float(np.linalg.norm(ug-G(T)@u@G(0).conj().T)),
       'Kubo_vs_centered_response_error':float(response)}

def main():
    balanced=shape((1.,-.58,-.42))
    unbalanced=shape((1.,.6,-.2))
    assert abs(balanced.sum())<1e-13
    mid=1.37
    a,v=field(mid,.2,unbalanced)
    ag,vg=field(mid,.2,unbalanced,True)
    assert np.linalg.norm(H(ag,vg)-
        (G(mid)@H(a,v)@G(mid).conj().T-
         np.diag(np.repeat(cdot(mid),2))))<1e-12
    # Gauge-invariant lattice electric field E_j = -Adot_j - (V_j-V_(j+1)).
    physicalE=-.2*fdot(mid)*unbalanced
    agdot=.2*fdot(mid)*unbalanced+cdot(mid)-np.roll(cdot(mid),-1)
    gaugedE=-agdot-(vg-np.roll(vg,-1))
    assert np.linalg.norm(gaugedE-physicalE)<1e-12
    assert abs(np.exp(1j*sum(ag))-np.exp(1j*sum(a)))<1e-12
    # Pure time-dependent U1 gauge has E=0 and no physical response.
    pure=evolve(0.,np.zeros(N),gauge=True)
    base=expm(-1j*H0*T)
    assert np.linalg.norm(pure-G(T)@base@G(0).conj().T)<1e-4

    out={'three_balanced':scenario(balanced),
         'three_unbalanced':scenario(unbalanced)}
    assert out['three_balanced']['local_density_change']>1e-4
    assert abs(out['three_balanced']['drive_wilson_angle_at_midpoint'])<1e-13
    conv=[]
    for steps in (90,180,360):
        z=scenario(balanced,steps)
        conv.append((steps,z['time_dependent_gauge_error'],z['Kubo_vs_centered_response_error']))
    assert conv[0][1]>3.8*conv[1][1] and conv[1][1]>3.8*conv[2][1]
    assert conv[0][2]>3.7*conv[1][2] and conv[1][2]>3.7*conv[2][2]
    out['step_refinement']=conv
    print(json.dumps(out,indent=2))
    print('PASS finite driven Wilson-Dirac gauge, CAR, Ward, Dyson/Kubo, balanced Wilson negative control')
    print('OPEN continuum Hadamard, full Maxwell/Einstein, physical MHD')
if __name__=='__main__':main()
