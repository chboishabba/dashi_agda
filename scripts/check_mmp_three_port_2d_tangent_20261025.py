#!/usr/bin/env python3
"""Independent 2D coupled Dirac/Maxwell tangent derivative + gauge checks.

Consumes the same source-selected Wilson Dirac and compact plaquette action
as check_mmp_three_port_2d_compact_u1_20261025.py. Tests central-difference
nonlinear evolution and verifies gauge-covariance of a driven initial-value
problem, not just a static Wilson holonomy.
"""
import json
import numpy as np
from scipy.integrate import solve_ivp
import check_mmp_three_port_2d_compact_u1_20261025 as m

H1=[]
H2=[]
for a,(s,k,d) in enumerate(m.endpoints):
    h1=np.zeros_like(m.H0)
    h2=np.zeros_like(m.H0)
    block=m.B[d]
    h1[2*s:2*s+2,2*k:2*k+2]=1j*block
    h1[2*k:2*k+2,2*s:2*s+2]=-1j*block.conj().T
    h2[2*s:2*s+2,2*k:2*k+2]=-block
    h2[2*k:2*k+2,2*s:2*s+2]=-block.conj().T
    H1.append(h1);H2.append(h2)
H1=np.array(H1);H2=np.array(H2)
CURV=np.array([np.trace(m.P0@h2).real for h2 in H2])
assert np.linalg.norm(m.links_current(m.H0,m.P0)-
                      np.array([np.trace(m.P0@h1).real for h1 in H1]))<1e-12


def linear(t,y,amp,magnetic=True):
    dp,dtheta,de,dq,_=m.unpack(y)
    dh=np.tensordot(dtheta,H1,axes=(0,0))
    pdot=-1j*(m.H0@dp-dp@m.H0+dh@m.P0-m.P0@dh)
    dj=np.array([np.trace(dp@h1).real for h1 in H1])+dtheta*CURV
    jex=m.external(t,amp)
    magnetic_force=(m.C.T@m.C@dtheta)/m.G2 if magnetic else np.zeros(m.ECOUNT)
    return m.pack(pdot,m.G2*de,-dj-magnetic_force+jex,m.D@jex,0.)


def tangent(amp,t,magnetic=True):
    s=solve_ivp(lambda x,y:linear(x,y,amp,magnetic),(0,t),
                np.zeros_like(m.Y0),method='DOP853',rtol=1e-10,
                atol=1e-11,max_step=.05)
    assert s.success,s.message
    return m.unpack(s.y[:,-1])


def centered(port,t,h):
    amp=np.zeros(3)
    amp[port]=h
    a=m.evolve(amp,t).y[:,-1]
    b=m.evolve(-amp,t).y[:,-1]
    return m.unpack((a-b)/(2*h))


def dynamic_gauge():
    phi=np.array([.26*np.sin(2*np.pi*x/m.L)+.09*np.cos(2*np.pi*y/m.L)
                  for x in range(m.L) for y in range(m.L)])
    u=np.diag(np.repeat(np.exp(1j*phi),2))
    gauge_angle=m.D.T@phi
    p0=u@m.P0@u.conj().T
    init=m.pack(p0,gauge_angle,np.zeros(m.ECOUNT),np.zeros(m.S),0.)
    amp=(.15,-.13,.095)
    sol=solve_ivp(lambda t,y:m.rhs(t,y,amp),(0,3.1),init,
                  method='DOP853',rtol=1e-10,atol=1e-11,max_step=.05)
    assert sol.success
    ordinary=m.evolve(amp,t=3.1)
    q,t,e,r,w=m.unpack(ordinary.y[:,-1])
    q2,t2,e2,r2,w2=m.unpack(sol.y[:,-1])
    return {'car_state':float(np.linalg.norm(q2-u@q@u.conj().T)),
            'link_angles':float(np.linalg.norm(t2-t-gauge_angle)),
            'electric_links':float(np.linalg.norm(e2-e)),
            'external_charge':float(np.linalg.norm(r2-r)),
            'energy_work':float(abs(w2-w)),
            'plaquettes':float(np.linalg.norm(m.C@(t2-t)))}


def main():
    tests=[]
    for time in (1.7,m.T):
        for i in range(3):
            amp=np.eye(3)[i]
            state=tangent(amp,time)
            dp,theta,efield,qext,_=state
            lin_charge=float(abs(np.trace(dp)))
            gauss=float(np.linalg.norm(m.D@efield-m.local_density(dp)-qext))
            errors=[]
            for eps in (.04,.02):
                fd=centered(i,time,eps)
                errors.append(float(np.linalg.norm(
                    m.local_density(fd[0])-m.local_density(dp))))
            if time < m.WINDOWS[i][0]:
                assert np.linalg.norm(dp)<1e-10 and max(errors)<1e-9
            else:
                assert errors[1]<2e-5,(time,i,errors)
                if errors[0]>1e-10:
                    assert errors[0]>3.7*errors[1],(time,i,errors)
            assert gauss<1e-10 and lin_charge<1e-10
            tests.append({'time':time,'port':i+1,
                    'density_linear_norm':float(np.linalg.norm(m.local_density(dp))),
                    'linear_gauss_norm':gauss,
                    'central_diff_error_eps_0_04':errors[0],
                    'central_diff_error_eps_0_02':errors[1]})
    amp=np.array(m.AMPLITUDES)
    joint=tangent(amp,m.T)
    singles=[tangent(np.eye(3)[i]*amp[i],m.T) for i in range(3)]
    superposition=float(np.linalg.norm(joint[0]-sum(p[0] for p in singles)))
    assert superposition<1e-10
    no_mag=tangent(amp,m.T,magnetic=False)
    induced_magnetic=float(np.linalg.norm(joint[2]-no_mag[2]))
    assert induced_magnetic>1e-5
    dyn=dynamic_gauge()
    assert max(dyn.values())<1e-9,dyn
    out={'independent_retarded_port_tests':tests,
         'three_port_linear_superposition_error':superposition,
         'magnetic_force_effect_on_linear_electric_links':induced_magnetic,
         'nonlinear_dynamic_local_gauge_covariance':dyn}
    print(json.dumps(out,indent=2))
    print('PASS: coupled 2D magnetic/fermion tangent, quadratic response convergence, causal control, nonlinear gauge covariance')
    print('NOT CLAIMED: continuum microcausality, 3+1D Maxwell-MHD, 4D Hadamard/Einstein')

if __name__=='__main__': main()
