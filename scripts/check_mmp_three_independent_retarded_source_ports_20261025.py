#!/usr/bin/env python3
"""Three independently timed U1 Wilson-Dirac source pulses and causal Kubo.

Prescribed finite EM link fields (NOT three Maxwell-MHD material plasmas).
Original relative-Cauchy/charged Dirac sources Sanders 2009 and Zahn 2015.
"""
import json
import numpy as np
from scipy.linalg import expm

N=9
D=2*N
T=3.2
Z=np.diag([1.,-1.]).astype(complex)
X=np.array([[0,1],[1,0]],complex)
B=-.31*(.55*Z+1j*X)
I=np.eye(D,dtype=complex)
positions=np.arange(N)
pulses=[(.2,1.18),(1.04,2.12),(2.28,3.04)]
shapes=[]
for center in (1,4,7):
    distance=np.minimum(abs(positions-center),N-abs(positions-center))
    g=np.exp(-distance**2/(2*.55**2))
    shapes.append(g/g.sum())
shapes=np.array(shapes)
def f(i,t):
    a,b=pulses[i]
    return np.sin(np.pi*(t-a)/(b-a))**2 if a<t<b else 0.
def A(t,amps):
    return (np.asarray(amps)*np.array([f(i,t) for i in range(3)]))@shapes
def H(a=None):
    if a is None:a=np.zeros(N)
    h=np.zeros((D,D),complex)
    for j in range(N):
        k=(j+1)%N
        m=.85+.095*np.cos(2*np.pi*j/N)+.06*np.sin(4*np.pi*j/N)
        h[2*j:2*j+2,2*j:2*j+2]=m*Z
        h[2*j:2*j+2,2*k:2*k+2]=B*np.exp(1j*a[j])
        h[2*k:2*k+2,2*j:2*j+2]=(B*np.exp(1j*a[j])).conj().T
    return h
H0=H()
e,v=np.linalg.eigh(H0)
P0=v[:,e<0]@v[:,e<0].conj().T
assert sum(e<0)==N
def evolved(amps,end,stepsize=.01):
    steps=int(np.ceil(end/stepsize))
    dt=end/steps
    u=I.copy()
    for k in range(steps):
        u=expm(-1j*H(A((k+.5)*dt,amps))*dt)@u
    return u
def n(P):
    return np.array([np.trace(P[2*j:2*j+2,2*j:2*j+2]).real for j in range(N)])
def dH(i):
    out=np.zeros((D,D),complex)
    for j in range(N):
        k=(j+1)%N
        b=1j*shapes[i,j]*B
        out[2*j:2*j+2,2*k:2*k+2]=b
        out[2*k:2*k+2,2*j:2*j+2]=b.conj().T
    return out
def response(i,end,stepsize=.01):
    steps=int(np.ceil(end/stepsize))
    dt=end/steps
    comm=dH(i)@P0-P0@dH(i)
    delta=np.zeros((D,D),complex)
    for k in range(steps):
        t=(k+.5)*dt
        if f(i,t)==0:continue
        u=expm(-1j*H0*(end-t))
        delta+=(-1j*dt*f(i,t))*(u@comm@u.conj().T)
    return n(delta)
def finite_difference(i,end,h=.0015):
    amps=np.zeros(3)
    amps[i]=h
    uplus=evolved(amps,end)
    amps[i]=-h
    uminus=evolved(amps,end)
    return (n(uplus@P0@uplus.conj().T)-
            n(uminus@P0@uminus.conj().T))/(2*h)
def main():
    rows={}
    for end in (1.7,T):
        values=[]
        for j in range(3):
            q=response(j,end)
            err=np.linalg.norm(q-finite_difference(j,end))
            assert err<1.5e-5
            assert abs(q.sum())<1e-12
            values.append({'source':j+1,'response_norm':float(np.linalg.norm(q)),
                           'port_response':[float(q[k]) for k in (1,4,7)],
                           'Kubo_difference_error':float(err)})
        rows[str(end)]=values
    assert rows['1.7'][2]['response_norm']<1e-13
    assert rows[str(T)][2]['response_norm']>1e-5
    amps=(.18,-.14,.11)
    u=evolved(amps,T)
    p=u@P0@u.conj().T
    assert np.linalg.norm(u.conj().T@u-I)<1e-11
    assert np.linalg.norm(p@p-p)<1e-11
    assert abs(np.trace(p-P0))<1e-11
    work=float(np.trace(H0@(p-P0)).real)
    assert work>=-1e-10
    rows['three_sources']={'amplitudes':amps,
      'final_ground_state_energy_gain':work,
      'final_charge_error':float(np.trace(p-P0).real),
      'final_local_density_response':float(np.linalg.norm(n(p-P0)))}
    print(json.dumps(rows,indent=2))
    print('PASS: 3 independent time windows, future-supported source no-response, retarded 3x3 Kubo, CAR and work')
    print('OPEN: physical MHD, 4D global Hadamard and Einstein-Maxwell fixed point')
if __name__=='__main__':main()
