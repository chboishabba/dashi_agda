#!/usr/bin/env python3
"""Exact zero outside compact TT source, but current F8 Bessel inverse leaks.

TT source comes from LOCAL 4th order (P Q P - P tr(PQ)/2)
applied to compact Cinf spatial bump with support |x|<eps, so
TT_yy(r)=0 exactly when r>eps. Reconstruct same source Fourier
spectrum using SAME current moving F8 numerical 3D angular inversion.
This static null benchmark isolates cutoff/k-spacing errors without
wave PDE evolution, and is NOT a physical signal.
"""
import json,math
import numpy as np
from scipy.special import spherical_jn
from ksw668_f8_uvir_source_cutoff import source_transform
ORIGINAL_RECEIVER=1.8300210521210103-.008

def reconstruct(N_x=768,L=4.,eps=.024,r=ORIGINAL_RECEIVER,
                quadrature_nodes=192):
    if N_x<64 or N_x%2 or min(L,eps)<=0 or r<=eps:
        raise ValueError('outside-source even-grid diagnostic')
    k=2*math.pi*np.arange(0,N_x//2+1)/L
    dk=2*math.pi/L
    phihat=source_transform(eps*k,quadrature_nodes)
    kr=k*r
    angular=2*(2*spherical_jn(0,kr)/5-
        4*spherical_jn(2,kr)/7+spherical_jn(4,kr)/35)
    numerical=float(eps**4*dk/(4*math.pi**2)*np.sum(
        k**6*phihat*angular))
    return dict(N_x=N_x,L=L,eps=eps,r=r,
       original_F8_angular_Bessel_rule=True,
       exact_local_compact_TT_yy_outside_support=0.,
       discrete_TT_yy_reconstruction_outside_support=numerical,
       absolute_static_reconstruction_error=abs(numerical),
       original_moving_retarded_PDE_tested=False,
       B4_receiver_converged=False)

def audit():
    rows=[reconstruct(n) for n in (256,512,768)]
    q96=reconstruct(768,quadrature_nodes=96)
    q384=reconstruct(768,quadrature_nodes=384)
    diff=abs(q96['discrete_TT_yy_reconstruction_outside_support']-
             q384['discrete_TT_yy_reconstruction_outside_support'])
    assert diff<1e-7
    assert min(r['absolute_static_reconstruction_error'] for r in rows)>100
    return dict(results=rows,
      radial_quadrature_96_vs_384_difference=diff,
      current_source_inverse_failure_without_wave_evolution=True,
      full_3D_F8_receiver_accepted=False)

if __name__=='__main__':print(json.dumps(audit(),indent=2))
