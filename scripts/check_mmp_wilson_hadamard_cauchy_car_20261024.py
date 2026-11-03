#!/usr/bin/env python3
"""Fixed-background Wilson U1 transport, finite CAR Cauchy state difference.
DASHI native exact Wilson owner: CompactLieLatticeGauge.
External Hadamard math: Gerard/Stoskopf, Capoferri/Murro and Zahn.
This finite test is NOT a globally Hadamard 4D Dirac state.
"""
import json
import numpy as np
L=7.;spin=.5;beta=.17
modes=np.arange(-30,31)
e=2*np.pi*(modes+spin-beta)/L
P0=np.diag((e<0).astype(float)).astype(complex)
P1=P0.copy()
for n in (1,3):
    index=int(np.where(modes==n)[0][0])
    assert P0[index,index]==0.
    P1[index,index]=1.
D=P1-P0
eye=np.eye(len(modes))
assert np.linalg.norm(P0@P0-P0)<1e-14
assert np.linalg.norm(P1@P1-P1)<1e-14
assert np.linalg.norm((eye-P1)@(eye-P1)-(eye-P1))<1e-14
assert np.linalg.eigvalsh(P0).min()>=-1e-13
assert np.linalg.eigvalsh(P1).max()<=1+1e-13
assert np.linalg.matrix_rank(D)==2
def psi(x,t):
    x=np.asarray(x)
    return np.exp(2j*np.pi*(modes[:,None]+spin)*x[None,:]/L-1j*e[:,None]*t)/np.sqrt(L)
def chi(x):return .31*np.sin(2*np.pi*x/L)+.16*np.cos(4*np.pi*x/L)
def K(x,y,t,s):
    return psi(x,t).T@D@psi(y,s).conj()
x=np.linspace(.1,3,47);y=np.linspace(1,5,51)
initial=K(x,y,1.3,-2.1)
gauge=np.exp(1j*(chi(x)[:,None]-chi(y)[None,:]))
parallel=np.exp(1j*2*np.pi*beta*(y[None,:]-x[:,None])/L)
parallel_g=parallel/gauge
err=np.max(np.abs(parallel*initial-parallel_g*gauge*initial))
assert err<1e-12
t=2.71
U=np.diag(np.exp(-1j*e*t))
time_err=np.linalg.norm(U@D@U.conj().T-D)
assert time_err<1e-12
density_error=np.max(np.abs(np.diag(K(x,x,0,0))-2/L))
assert density_error<1e-12
results={'finite_car_modes':len(modes),'difference_rank':2,
 'max_gauge_dressed_kernel_error':float(err),
 'max_time_evolution_error':float(time_err),
 'diagonal_density_error':float(density_error),
 'open':'true 4D Hadamard WF, charged spin-c physical reference state and Einstein-Maxwell stress/current'}
if __name__=='__main__':
    print(json.dumps(results,indent=2))
    print('PASS finite CAR/Cauchy/smooth 2-point difference/U1 Wilson dressing')
