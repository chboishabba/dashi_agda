#!/usr/bin/env python3
"""F8 independent UV cutoff and IR/frequency-spacing axes for spatial FFT.

Current k_j=2*pi*j/L, so kmax=pi*Nx/L but dk=2*pi/L
remains fixed when Nx grows at the same L. At original receiver r,
large-kr spherical Bessel sampling phase step is dk*r.

Targets U_ref=100 and phase increment <=0.25 are numerical design
criteria (not rigorous universal lower bounds on other algorithms).
"""
import json
import math
ORIGINAL_RECEIVER=1.8300210521210103-.008

def grid(N_x=768,L=4.,eps=.024,r=ORIGINAL_RECEIVER):
    if N_x<=0 or N_x%2 or min(L,eps,r)<=0:
        raise ValueError('positive even periodic grid/radius/receiver')
    return dict(N_x=N_x,L=L,eps=eps,r=r,
       kmax=math.pi*N_x/L,dk=2*math.pi/L,
       u_max=eps*math.pi*N_x/L,du=eps*2*math.pi/L,
       large_kr_bessel_sample_phase_increment=2*math.pi*r/L,
       samples_per_large_kr_cycle=L/r,
       convergence_at_fixed_L_from_Nx_alone=False)

def design(u_target=100.,receiver_phase_step_target=.25,
           eps=.024,r=ORIGINAL_RECEIVER):
    if min(u_target,receiver_phase_step_target,eps,r)<=0:
        raise ValueError('positive numerical design targets')
    L=2*math.pi*r/receiver_phase_step_target
    N=math.ceil(u_target*L/(math.pi*eps))
    if N%2:N+=1
    d=grid(N,L,eps,r)
    assert d['u_max']>=u_target
    assert d['large_kr_bessel_sample_phase_increment']<=receiver_phase_step_target*(1+1e-12)
    return dict(target_scaled_U=u_target,target_large_kr_phase_step=receiver_phase_step_target,
       minimum_spatial_L_in_this_uniform_design=L,
       minimum_even_Nx_in_this_uniform_design=N,
       corresponding_grid=d,not_a_universal_numerical_lower_bound=True,
       suggested_solver='adaptive/oscillatory k quadrature plus 1D radial evolution per k',
       original_3d_receiver_convergence_accepted=False)

def audit():
    a=grid();b=grid(1536,L=4)
    assert math.isclose(a['dk'],b['dk']) and math.isclose(b['kmax'],2*a['kmax'])
    return dict(current=a,uniform_reference_design=design(),
       independent_UV_cutoff_and_IR_spacing_axes=True,
       original_a_t_receiver_weyl_accepted=False)

if __name__=='__main__':print(json.dumps(audit(),indent=2))
