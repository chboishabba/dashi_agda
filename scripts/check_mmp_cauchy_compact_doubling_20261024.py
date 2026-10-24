#!/usr/bin/env python3
"""Capoferri--Murro 2025 Remark 3.8(2) toy: finite-time compact doubling.

A specific massless 1+1D chiral Dirac evolution with smooth, compactly
supported initial data. On a circle [-R,R) with periodic identified endpoints
(an elementary local compactification surrogate), its solution equals the
solution on R while causal support stays away from the gluing seam.
Local two-point kernels constructed from the SAME propagated finite-rank
modes agree in the causal interior.

The true 4D double is a doubled compact *three-dimensional spatial* collar,
not literally this one-dimensional circle; this test checks the local
finite-speed and uniqueness mechanism only. No Hadamard state or renormalized
Einstein-Maxwell-Dirac solution is inferred.
Original authority: M. Capoferri, S. Murro (2025) Remark 3.8(2),
DOI 10.1002/mana.12032. General free Dirac Hadamard existence:
C. Gerard, T. Stoskopf (2022), DOI 10.1142/S0129055X22500088.
"""
import json
import numpy as np
from pathlib import Path

R=10.0
a=1.6
b=2.4
T=5.0
assert a+b+T<R

def bump(x):
    x=np.asarray(x,dtype=float)
    u=x/a
    value=np.zeros(x.shape)
    mask=np.abs(u)<1
    value[mask]=np.exp(-1/(1-u[mask]**2))
    return value

def seed(x):
    x=np.asarray(x,dtype=float)
    return np.stack((bump(x)*(1+0.23j*x/a),
                     bump(x)*np.exp(0.4j*x/a)))

def evolve(t,x,periodic=False):
    x=np.asarray(x,dtype=float)
    r=x-t
    l=x+t
    if periodic:
        return np.stack((sum(seed(r+2*R*k)[0] for k in range(-2,3)),
                         sum(seed(l+2*R*k)[1] for k in range(-2,3))))
    return np.stack((seed(r)[0],seed(l)[1]))

def two_point(t,x,s,y,periodic=False):
    # Positive finite-rank mode kernel, NOT a globally Hadamard 2pt function.
    aa=evolve(t,x,periodic)
    bb=evolve(s,y,periodic)
    return np.einsum('ix,iy->xy',aa,np.conjugate(bb))

def main():
    grid=np.linspace(-b,b,151)
    times=[-T,-2.5,0.,2.5,T]
    max_error=0.
    norm_error=0.
    xwhole=np.linspace(-R,R,10001,endpoint=False)
    for t in times:
        line=evolve(t,grid)
        doubled=evolve(t,grid,True)
        max_error=max(max_error,float(np.max(np.abs(line-doubled))))
        assert max_error<2e-14
        lhs=np.trapezoid(np.sum(np.abs(evolve(t,xwhole))**2,axis=0),xwhole)
        rhs=np.trapezoid(np.sum(np.abs(evolve(t,xwhole,True))**2,axis=0),xwhole)
        norm_error=max(norm_error,abs(lhs-rhs))
        assert norm_error<1e-13
    xs=np.linspace(-b,b,51)
    kernel_err=0.
    for t,s in ((0,0),(-T,3),(T,-T)):
        err=np.max(np.abs(two_point(t,xs,s,xs)-
                             two_point(t,xs,s,xs,True)))
        kernel_err=max(kernel_err,float(err))
    assert kernel_err<1e-13
    # DELIBERATE negative control after the causal hull reaches the seam:
    later=10.5
    near_edge=-9.5
    line=evolve(later,np.array([near_edge]))
    circle=evolve(later,np.array([near_edge]),True)
    mismatch=float(np.max(np.abs(line-circle)))
    assert mismatch>1e-2
    # No signal before the 1+1 light cone reaches a distant observation site.
    before=evolve(3,np.array([-9.,9.]))
    assert np.max(np.abs(before))<1e-13
    out={'theorem_root':'Capoferri--Murro 2025 Remark 3.8(2)',
         'operator':'1+1 massless chiral Dirac on R and periodic circle',
         'R':R,'support_radius':a,'observation_radius':b,'time_bound':T,
         'strict_causal_gap':R-a-b-T,
         'max_local_evolution_difference':max_error,
         'max_local_mode_two_point_difference':kernel_err,
         'max_full_interval_norm_difference_pre_gluing':norm_error,
         'outside_safe_cone_periodic_return_discrepancy':mismatch,
         'scope':'finite-time compact-support Cauchy solution identity, not globally Hadamard renormalization'}
    if __name__=='__main__':
        print(json.dumps(out,indent=2))
        print('PASS: local finite-time Cauchy doubling, conserved norms, finite-rank kernels and negative wrap control')
    return out
if __name__=='__main__':main()
