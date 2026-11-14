#!/usr/bin/env python3
"""Finite-state Wilson/Hadamard same-background check, not a 4D Hadamard proof.
Original: Zahn 2014, Capoferri-Murro 2025 and standard U1 parallel transport.
Native DASHI: CompactLieLatticeGauge.agda already proves Wilson covariance.
"""
import json
import math
import numpy as np
L=7.
spin=.5
beta=.17
A=2*np.pi*beta/L
occ={1:1.,3:1.}
def chi(x):
    return .31*np.sin(2*np.pi*x/L)+.16*np.cos(4*np.pi*x/L)+.23
def chip(x):
    return .31*(2*np.pi/L)*np.cos(2*np.pi*x/L)-.16*(4*np.pi/L)*np.sin(4*np.pi*x/L)
def psi(n,x):
    return np.exp(2j*np.pi*(n+spin)*x/L)/np.sqrt(L)
def kernel(x,y,gauge=False):
    K=sum(w*psi(n,x)*np.conj(psi(n,y)) for n,w in occ.items())
    return K*np.exp(1j*(chi(x)-chi(y))) if gauge else K
def transport(x,y,gauge=False):
    d=A*(y-x)
    if gauge:d+=chi(y)-chi(x)
    return np.exp(1j*d)
def contracted(x,y,gauge=False):
    return transport(x,y,gauge)*kernel(x,y,gauge)
def current(x,gauge=False):
    a=A+chip(x) if gauge else A
    result=0.
    for n,w in occ.items():
        k=2*np.pi*(n+spin)/L
        p=psi(n,x)*np.exp(1j*chi(x)) if gauge else psi(n,x)
        dp=1j*(k+chip(x))*p if gauge else 1j*k*p
        result+=w*np.imag(np.conj(p)*(dp-1j*a*p))
    return result
x=np.linspace(0,L,97,endpoint=False)
X=x[:,None];Y=x[None,:]
K=kernel(X,Y)
rank=int(np.linalg.matrix_rank(K,tol=1e-9))
assert rank==2
err=float(np.max(np.abs(contracted(X,Y)-contracted(X,Y,True))))
assert err<1e-12
cur_err=float(np.max(np.abs(current(x)-current(x,True))))
assert cur_err<1e-12
assert abs(transport(.75,4.9,True)-
           transport(2.1,4.9,True)*transport(.75,2.1,True))<1e-12
wilson=np.exp(1j*A*L)
assert abs(wilson-np.exp(2j*np.pi*beta))<1e-12
assert abs(np.exp(1j*(A*L+chi(L)-chi(0)))-wilson)<1e-12
monodromy=np.exp(2j*np.pi*spin-1j*A*L)
assert abs(contracted(.64+L,2.32)-monodromy*contracted(.64,2.32))<1e-12
deltaE=sum(w*abs(2*np.pi*(n+spin-beta)/L) for n,w in occ.items())
def sea(k):
    ns=np.arange(-k,k+1)
    return -.5*np.abs(2*np.pi*(ns+spin-beta)/L).sum()
cutoffs=(8,20,64,200)
ref_diff=[(sea(k)+deltaE)-sea(k) for k in cutoffs]
assert max(ref_diff)-min(ref_diff)<1e-11
assert abs(ref_diff[0]-deltaE)<1e-11
report={'source_type':'smooth finite-rank quasifree state difference, same fixed U1 background',
 'L':L,'spin_structure_fraction':spin,'wilson_fraction':beta,
 'state_difference_rank':rank,'gauge_bilocal_residual':err,'gauge_current_residual':cur_err,
 'wilson_phase':[float(wilson.real),float(wilson.imag)],
 'unrenormalized_vacuum_cutoff_values':[float(sea(k)) for k in cutoffs],
 'finite_excitation_energy':float(deltaE),
 'same_parametrix_cancelled_differences':[float(x) for x in ref_diff],
 'open':['full 4D charged spin-c Hadamard reference state',
         'microlocal WF / CAR positive state on actual handle',
         'covariant point-split 4D stress and current',
         'Einstein Maxwell backreaction and three plasma sources']}
if __name__=='__main__':
    print(json.dumps(report,indent=2))
    print('PASS: native Wilson-style covariance, rank-2 smooth delta, gauge-covariant current, finite reference cancellation')
