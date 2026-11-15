#!/usr/bin/env python3
"""Independent linearized retarded source-response for the 3+1D finite model.

Represents the fermionic CAR projector tangent in exact H0 eigenbasis
rather than linearly perturbing occupied orbital phases. This removes
unphysical occupied-occupied gauge rotations from physical δP.
The gauge field remains *classical*; no 4D Hadamard/microlocal theorem.
"""
import json
import numpy as np
import check_mmp_3d_maxwell_dirac_three_ports_20261025 as m

O=m.V0
U=m.vectors[:,m.DIM//2:]
NO=O.shape[1]
NU=U.shape[1]
assert NU==NO==54
EXC=m.spectrum[NO:,None]-m.spectrum[None,:NO]
M=np.empty((m.ECOUNT,NU,NO),complex)
CURV=np.empty(m.ECOUNT)
for a,(s,k,d) in enumerate(m.endpoints):
    t=slice(m.SPIN*s,m.SPIN*s+m.SPIN)
    u=slice(m.SPIN*k,m.SPIN*k+m.SPIN)
    # dH/dtheta, with same link orientation and Hamiltonian as nonlinear owner.
    h1=1j*m.B[d]
    M[a]=U[t].conj().T@h1@O[u]+U[u].conj().T@h1.conj().T@O[t]
    CURV[a]=-2*np.real(np.vdot(O[t],m.B[d]@O[u]))
K=np.empty((m.S,NU,NO),complex)
for s in range(m.S):
    t=slice(m.SPIN*s,m.SPIN*s+m.SPIN)
    K[s]=U[t].conj().T@O[t]

def density(z):
    return 2*np.real(np.einsum('suo,uo->s',K.conj(),z))

def current(z,theta):
    return 2*np.real(np.einsum('euo,uo->e',M.conj(),z))+theta*CURV

# y includes 54x54 coherent occupied/unoccupied projector block,
# 81 theta, 81 electric field, 27 external source charges.
ZSIZE=NO*NU

def pack(z,theta,e,q):
    return np.r_[z.ravel(),np.asarray(theta,complex),np.asarray(e,complex),np.asarray(q,complex)]

def unpack(y):
    return (y[:ZSIZE].reshape(NU,NO),
      y[ZSIZE:ZSIZE+m.ECOUNT].real,
      y[ZSIZE+m.ECOUNT:ZSIZE+2*m.ECOUNT].real,
      y[ZSIZE+2*m.ECOUNT:ZSIZE+2*m.ECOUNT+m.S].real)

Y0=np.zeros(ZSIZE+2*m.ECOUNT+m.S,complex)

def rhs(t,y,amps,with_magnetic=True,with_matter=True):
    z,theta,e,q=unpack(y)
    pert=np.tensordot(theta,M,axes=(0,0))
    dz=-1j*(EXC*z+pert)
    j=current(z,theta) if with_matter else 0.
    magnetic=m.C.T@m.C@theta/m.G2 if with_magnetic else 0.
    ext=m.source(t,amps)
    return pack(dz,m.G2*e,-j-magnetic+ext,m.D@ext)

def integrate(amps,t=m.FINISH,dt=.025,with_magnetic=True,with_matter=True):
    points=np.linspace(0,t,int(np.ceil(t/dt))+1)
    y=Y0.copy()
    for a,b in zip(points[:-1],points[1:]):
        step=b-a
        k1=rhs(a,y,amps,with_magnetic,with_matter)
        k2=rhs(a+step/2,y+step*k1/2,amps,with_magnetic,with_matter)
        k3=rhs(a+step/2,y+step*k2/2,amps,with_magnetic,with_matter)
        k4=rhs(b,y+step*k3,amps,with_magnetic,with_matter)
        y+=step*(k1+2*k2+2*k3+k4)/6
    return unpack(y)

def centered_source_derivative(port,t,eps,dt=.006):
    a=np.zeros(3)
    a[port]=eps
    plus=m.integrate(a,finish=t,dt=dt)
    minus=m.integrate(-a,finish=t,dt=dt)
    p=m.densities(m.unpack(plus)[0])
    q=m.densities(m.unpack(minus)[0])
    return (p-q)/(2*eps)

def main():
    tests=[]
    for t in (m.FINISH,):
      for i in range(3):
        a=np.zeros(3);a[i]=1.
        z,theta,e,q=integrate(a,t)
        gauss=np.linalg.norm(m.D@e-density(z)-q)
        charges=float(abs(sum(density(z))))
        linear_density=density(z)
        e1=float(np.linalg.norm(centered_source_derivative(i,t,.30)-linear_density))
        e2=float(np.linalg.norm(centered_source_derivative(i,t,.15)-linear_density))
        assert gauss<1e-9,(t,i,gauss)
        assert charges<1e-9,(t,i,charges)
        if t<m.WINDOWS[i][0]:
            assert np.linalg.norm(z)<1e-12 and e1<1e-9 and e2<1e-9
        else:
            assert e2<1e-5,(t,i,e1,e2)
            if e1>1e-8:assert e1>2.4*e2,(t,i,e1,e2)
        print('validated',t,i,'errors',e1,e2,flush=True)
        tests.append({'t':t,'port':i+1,'linearized_density_norm':float(np.linalg.norm(linear_density)),
                      'linearized_gauss_error':float(gauss),
                      'centered_fd_error_eps_0_30':e1,'centered_fd_error_eps_0_15':e2})
    joint=integrate(m.AMPS)
    split=[integrate(np.eye(3)[i]*m.AMPS[i]) for i in range(3)]
    superposition=float(np.linalg.norm(joint[0]-sum(x[0] for x in split)))
    assert superposition<1e-9
    without_curl=integrate(m.AMPS,with_magnetic=False)
    without_current=integrate(m.AMPS,with_matter=False)
    magnetic_effect=float(np.linalg.norm(joint[2]-without_curl[2]))
    discarded_matter_gauss=float(np.linalg.norm(m.D@without_current[2]-
                                             density(without_current[0])-without_current[3]))
    assert magnetic_effect>1e-5 and discarded_matter_gauss>1e-5
    data={'tests':tests,'linear_superposition_error':superposition,
          'magnetic_curl_ablation_electric_difference':magnetic_effect,
          'fermion_feedback_ablation_gauss_violation':discarded_matter_gauss}
    print(json.dumps(data,indent=2))
    print('PASS: 3D linearized CAR projector density, 3 independent retarded ports, Gauss, finite-difference coupling and ablations')

if __name__=='__main__':main()
