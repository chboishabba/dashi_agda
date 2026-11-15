#!/usr/bin/env python3
"""F8 actual original compact C-infinity radial TT source: UV/IR scale audit.

Radial bump phi(r) proportional to exp(-1/(1-(r/eps)^2)) for r<eps,
zero else, normalized to unit 3D integral; same as original F8 code.
4th-order local TT generator -> weighted k^10|phihat|^2 L2 source norm;
two more spatial derivatives -> weighted k^14|phihat|^2 source diagnostic.
u=eps*k. Reference [0,100] MOMENTS are POSITIVE LOWER BOUNDS on full
moments. Thus fraction M[0,u_cut]/M[0,100] is an UPPER BOUND on the
captured full spectral norm fraction, modulo numerical quadrature accuracy.
DO NOT infer from source norm alone a Weyl receiver truncation bound.
"""
import functools
import json
import math
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import cumulative_simpson

EPS_DEFAULT=0.024
L_DEFAULT=4.
U_REFERENCE=100.

def source_transform(u,quad_nodes=256):
    u=np.asarray(u,dtype=np.float64)
    if np.any(u<0):raise ValueError("nonnegative spatial frequencies")
    if quad_nodes<32:raise ValueError("radial quadrature too small")
    x,w=leggauss(quad_nodes)
    r=(x+1)/2
    weight=w*r*r*np.exp(-1/(1-r*r))/2
    weight/=weight.sum()
    return np.sum(weight[:,None]*np.sinc(r[:,None]*u[None,:]/np.pi),axis=0)

@functools.lru_cache(maxsize=8)
def moment_table(quad_nodes=256,samples=5001):
    if samples<1001 or samples%2==0:raise ValueError("odd sufficient sample count")
    u=np.linspace(0,U_REFERENCE,samples)
    ft=source_transform(u,quad_nodes)
    tables={}
    for p in (10,14):
        cum=np.r_[0.,cumulative_simpson(u**p*ft*ft,x=u)]
        tables[p]=(cum,float(cum[-1]))
    return u,ft,tables

def audit(quad_nodes=256,samples=5001,eps=EPS_DEFAULT,
          L=L_DEFAULT,N=(256,512,768)):
    if eps<=0 or L<=0:raise ValueError("positive eps and L")
    u,ft,tables=moment_table(quad_nodes,samples)
    cuts=[float(eps*math.pi*n/L) for n in N]
    if max(cuts)>=U_REFERENCE:raise ValueError("cutoff exceeds fixed positive reference")
    out={}
    for p in (10,14):
        cum,reference=tables[p]
        fraction=[float(np.interp(c,u,cum)/reference) for c in cuts]
        bounds=(0.,1.,2.,4.,8.,16.,32.,64.,U_REFERENCE)
        shells=[{'scaled_u_band':[a,b],
                 'reference_fraction':float((np.interp(b,u,cum)-
                     np.interp(a,u,cum))/reference)}
                 for a,b in zip(bounds[:-1],bounds[1:])]
        out[str(p)]={'weight':f'u^{p} |phihat(u)|^2',
          'positive_reference_integral_u0_100':reference,
          'captured_fraction_UPPER_BOUND_vs_full':fraction,
          'omitted_fraction_LOWER_BOUND_vs_full':[1-z for z in fraction],
          'dyadic_reference_shells':shells,
          'IR_analytic_bound':f'integral_0^U u^{p}|phihat|^2 du <= U^{p+1}/{p+1}',
          'IR_exponent':p+1,
          'full_spectrum_integral_computed':False}
    return dict(model='original a=t 3D compact TT source Fourier bump',
      scope='source spectrum, not time-dependent propagator or Weyl receiver',
      bump='Cinf exp(-1/(1-r^2)) radial compact normalized 3D',
      source_transform_at_zero=float(ft[0]),
      IR_bound_from_nonnegative_probability_bump=True,
      epsilon=eps,periodic_spatial_L=L,grid_N=list(N),
      grid_scaled_k_cutoffs=cuts,reference_scaled_U=U_REFERENCE,
      radial_quadrature_nodes=quad_nodes,
      radial_frequency_samples=samples,moments=out,
      physical_receiver_tested=False,
      Weyl_receiver_convergence_certified=False,
      Agda_pinned_kernel_verified=False)

def crosscheck():
    a=audit(192);b=audit(384)
    drift={}
    for p in ('10','14'):
        drift[p]=max(abs(x-y) for x,y in zip(
          a['moments'][p]['captured_fraction_UPPER_BOUND_vs_full'],
          b['moments'][p]['captured_fraction_UPPER_BOUND_vs_full']))
    assert max(drift.values())<1e-7
    assert b['moments']['10']['captured_fraction_UPPER_BOUND_vs_full'][-1]<.012
    assert b['moments']['14']['captured_fraction_UPPER_BOUND_vs_full'][-1]<2e-5
    return dict(**b,radial_quadrature_crosscheck_max_abs_drift=drift,
       source_spectral_cutoff_acceptance=False,
       original_receiver_3D_convergence_still_open=True)

if __name__=='__main__':
    print(json.dumps(crosscheck(),indent=2))
