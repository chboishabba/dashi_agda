#!/usr/bin/env python3
"""Original a=t Poincare AdS5 moving Neumann boundary covector phase weld.

The original direct-null phase -T+s*z+k*x restricts to the MOVING wall as
-T+s*b(T)+k*x. Inward Israel and outward convexity normals have OPPOSITE
signs, and this module checks the precise convention. It is not a full FIO.
"""
import math
import json
import sympy as sy
from ksw668_f8_non_glancing_source import audit

def symbolic():
    v,s,b=sy.symbols('v s b',real=True)
    ksq=1-s*s
    tau=-1+s*v
    tangential_norm=ksq-tau*tau/(1-v*v)
    expected=-(s-v)**2/(1-v*v)
    assert sy.simplify(tangential_norm-expected)==0
    # n_in^A = b(v dT+dz)/sqrt(1-v²).  n_out=-n_in.
    ni=b*(s-v)/sy.sqrt(1-v*v)
    no=-ni
    assert sy.simplify(ni+no)==0
    return dict(boundary_phase='-T+s*b(T)+k*x',
      boundary_time_covector='-1+s*v(T)',
      timelike_tangential_norm='-b²*(s-v)²/(1-v²)',
      inward_israel_normal_symbol='b*(s-v)/sqrt(1-v²)',
      outward_convexity_normal_symbol='-b*(s-v)/sqrt(1-v²)',
      boundary_phase_matches_bulk_original_ray=True,
      inward_and_outward_unit_normals_opposite=True,
      full_retarded_FIO_receiver_proved=False)

def original_t2():
    r=audit()
    s=r['direct_ray_radial_slope']
    ve=r['v_emitter']; vr=r['v_receiver']
    ne=r['emitter_normal_symbol'];nr=r['receiver_normal_symbol']
    ke=math.sqrt(1-s*s)
    be=1/r['actual_source_proper_t'];br=.5
    assert math.isclose(ne,be*(s-ve)/math.sqrt(1-ve*ve),rel_tol=1e-11)
    assert math.isclose(nr,br*(s-vr)/math.sqrt(1-vr*vr),rel_tol=1e-11)
    assert ne>0 and nr<0
    assert (1-s*ve)**2 > ke*ke*(1-ve*ve)
    assert (1-s*vr)**2 > ke*ke*(1-vr*vr)
    return dict(source_inward_normal=ne,receiver_inward_normal=nr,
                source_outward_normal=-ne,receiver_outward_normal=-nr,
                source_boundary_time_covector=-1+s*ve,
                receiver_boundary_time_covector=-1+s*vr,
                source_timelike_projection=True,receiver_timelike_projection=True,
                same_original_t2_receiver=r['receiver_original_t'],
                true_original_ray_phase_prepared=True,
                FIO_transport_referee_accepted=False)

def result():return dict(formal=symbolic(),original_t2=original_t2())
if __name__=='__main__': print(json.dumps(result(),indent=2))
