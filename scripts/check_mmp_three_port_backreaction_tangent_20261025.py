#!/usr/bin/env python3
"""Linear retarded three-port response of SAME coupled finite U(1)/Dirac system.

Independent finite-difference acceptance, NOT a 4D Hadamard response.
Original real-time classical-statistical gauge/fermion donors: Hebenstreit,
Berges, Gelfand (2013); Kasper, Hebenstreit, Berges (2014).
"""
import json
import numpy as np
from scipy.integrate import solve_ivp
import check_mmp_three_port_gauge_backreaction_20261025 as b

H1=[]
H2=[]
for j in range(b.N):
    k=(j+1)%b.N
    one=np.zeros((b.D,b.D),complex)
    two=np.zeros_like(one)
    one[2*j:2*j+2,2*k:2*k+2]=1j*b.B
    one[2*k:2*k+2,2*j:2*j+2]=(-1j*b.B.conj().T)
    two[2*j:2*j+2,2*k:2*k+2]=-b.B
    two[2*k:2*k+2,2*j:2*j+2]=-b.B.conj().T
    H1.append(one);H2.append(two)
H1=np.array(H1)
H2=np.array(H2)
assert all(np.linalg.norm(H1[j]-H1[j].conj().T)<1e-14 for j in range(b.N))
assert all(np.linalg.norm(H2[j]-H2[j].conj().T)<1e-14 for j in range(b.N))
# The direct current derivative uses precisely the source-selected current.
assert np.linalg.norm([np.trace(b.P0@H1[j]).real-b.current(b.H0,b.P0)[j]
                       for j in range(b.N)])<1e-12
BASE_CURV=np.array([np.trace(b.P0@H2[j]).real for j in range(b.N)])


def tangent_rhs(t,y,amps,feedback=True):
    dp,da,de,dq,dwork=b.unpack(y)
    dh=np.einsum('j,jab->ab',da,H1)
    dP=-1j*(b.H0@dp-dp@b.H0+dh@b.P0-b.P0@dh)
    dj=np.array([np.trace(dp@H1[j]).real for j in range(b.N)])+da*BASE_CURV
    ext=b.external_current(t,amps)
    return b.pack(dP,b.G2*de,-dj+ext if feedback else ext,
                  ext-np.roll(ext,1),0.)


def integrate(amps,end,feedback=True):
    s=solve_ivp(lambda t,y:tangent_rhs(t,y,amps,feedback),(0,end),
                np.zeros_like(b.Y0),method='DOP853',rtol=1e-10,
                atol=1e-11,max_step=.045)
    assert s.success
    return b.unpack(s.y[:,-1])


def finite_difference(i,end,eps):
    amp=np.zeros(3);amp[i]=eps
    plus=b.simulate(amp,end)
    minus=b.simulate(-amp,end)
    return (plus.y[:,-1]-minus.y[:,-1])/(2*eps)


def main():
    rows=[]
    for t in (1.7,3.4):
        for i in range(3):
            amps=np.zeros(3);amps[i]=1.
            lin=integrate(amps,t)
            n1=b.density(lin[0])
            f1=b.unpack(finite_difference(i,t,.02))
            f2=b.unpack(finite_difference(i,t,.01))
            errors=[float(np.linalg.norm(b.density(f[0])-n1)) for f in (f1,f2)]
            if t<2.28 and i==2:
                assert np.linalg.norm(n1)<1e-11
            else:
                assert errors[1]<2e-5,(t,i,errors)
                if errors[0]>1e-9:
                    assert errors[0]>3.7*errors[1],(t,i,errors)
                else:
                    assert errors[0]<1e-9 and errors[1]<1e-9
            dp,da,de,dq,_=lin
            lin_gauss=float(np.max(abs(de-np.roll(de,1)-b.density(dp)-dq)))
            assert lin_gauss<2e-10
            assert abs(np.trace(dp))<2e-10
            rows.append({'time':t,'port':i+1,'linear_density_norm':float(np.linalg.norm(n1)),
                         'epsilon_0.02_error':errors[0],
                         'epsilon_0.01_error':errors[1],
                         'linear_gauss_error':lin_gauss})
    amps=np.array([.18,-.14,.11])
    joined=integrate(amps,3.4)
    partials=[integrate(np.eye(3)[i]*amps[i],3.4) for i in range(3)]
    superposition=float(np.linalg.norm(joined[0]-sum(x[0] for x in partials)))
    assert superposition<1e-10
    # Removing fermion feedback is deliberately a nonphysical control:
    # its field fails the full Gauss constraint once density responds.
    prescribed=integrate(amps,3.4,feedback=False)
    full=integrate(amps,3.4,feedback=True)
    induced_field=float(np.linalg.norm(full[2]-prescribed[2]))
    no_feedback_gauss=float(np.linalg.norm(prescribed[2]-np.roll(prescribed[2],1)-
                          b.density(prescribed[0])-prescribed[3]))
    assert induced_field>1e-4
    assert no_feedback_gauss>1e-4
    print(json.dumps({'linearized_three_port_receipt':rows,
          'port_superposition_residual':superposition,
          'full_minus_source_only_linear_electric_norm':induced_field,
          'source_only_gauss_violation':no_feedback_gauss},indent=2))
    print('PASS: exact coupled tangent equations match centered nonlinear response with quadratic error, retarded time support, superposition, Gauss')
    print('OPEN: physical 3+1D Maxwell/MHD, curved spin-c Hadamard/Einstein')
if __name__=='__main__':main()
