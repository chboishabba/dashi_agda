#!/usr/bin/env python3
"""KSW D2.B3: localised source -> actual scalar *test-field* receiver response.

Not a graviton, not real transport and not a self-gravitating Israel brane.
Uses the same ambient 5D Minkowski metric, cylindrical probe brane, and
same antipodal source/detector as ksw668_brane_bulk_shortcut_same_metric.py.
A free massless bulk scalar obeys (d_t^2 - nabla_4^2)phi = J in 4 spatial
dimensions. The brane source is an idealised point with positive coupling
q(t)=a[t_+ - 2(t-tau)_+ + (t-2tau)_+], a compact triangular switch.
A receiver measures lambda_det * phi at radius d from the point source.

With the 4-space-dimensional retarded fundamental solution,
 G_{4+1}^ret = -(1/(2*pi*d)) d/dd G_{2+1}^ret,
 G_{2+1}^ret = Theta(t-d)/(2*pi*sqrt(t^2-d^2)),
the response to a ramp source a*t_+ at distance d>0 is
 phi_ramp(t,d) = a*Theta(t-d)*sqrt(t^2-d^2)/(4*pi^2*d^2).
Hence the triangle's response is the second time-shift difference.

The earliest bulk front reaches the antipodal detector at 2R, and
a brane-constrained photon can arrive only after pi R. For any
0<tau<2(pi-2)R, there is an explicit common-detector time
2R+tau/2 before pi R with nonzero receiver response.

POINT SOURCE LIMIT: the field near the emitter is singular; receiver
d>0 finite. A finite-energy globally regular source requires spatial
smearing and finite-band detector modeling, still OPEN. A scalar with
chosen source/detector couplings is a physically meaningful classical
test-field example, not an observed graviton/emission mechanism.
No signal violates 5D causality or supplies free energy.

Original brane-shortcut context: R.R. Caldwell, D. Langlois (2001),
doi:10.1016/S0370-2693(01)00631-1; this flat-cylinder *new test model*
is NOT the paper's moving AdS5 cosmology.
"""
import argparse
import json
import math
import sympy as s

PI=math.pi

def truncated_radial_ramp(t,d):
    if not (math.isfinite(t) and math.isfinite(d)) or d<=0:
        raise ValueError("Finite source/receiver time and nonzero 4D spatial separation required")
    if t<=d:return 0.0
    return math.sqrt((t-d)*(t+d))

def retarded_receiver(t, distance, pulse_duration, emitter=1., detector=1.):
    if not all(math.isfinite(z) for z in (t,distance,pulse_duration,emitter,detector)):
        raise ValueError("Finite scalar source, coupling and detector inputs required")
    if distance<=0 or pulse_duration<=0 or emitter<=0 or detector<=0:
        raise ValueError("Positive radius, duration and nonzero source/detector coupling required")
    g=truncated_radial_ramp
    return (emitter*detector/(4*PI*PI*distance*distance)*
            (g(t,distance)-2*g(t-pulse_duration,distance)
                 +g(t-2*pulse_duration,distance)))

def symbolic_audit():
    t,r=s.symbols("t r",positive=True,real=True)
    green_2D_step=s.acosh(t/r)/(2*s.pi)
    green_4D_step=s.simplify(-s.diff(green_2D_step,r)/(2*s.pi*r))
    expect_step=t/(4*s.pi**2*r**2*s.sqrt(t**2-r**2))
    assert s.simplify(green_4D_step-expect_step)==0
    green_4D_ramp=s.sqrt(t*t-r*r)/(4*s.pi**2*r*r)
    assert s.simplify(s.diff(green_4D_ramp,t)-green_4D_step)==0
    assert s.simplify(
       s.diff(green_4D_ramp,t,2)-s.diff(green_4D_ramp,r,2)
        -3*s.diff(green_4D_ramp,r)/r)==0
    assert s.limit(green_4D_step,t,s.oo)==1/(4*s.pi**2*r**2)
    return {"source_recursion":"G_5^ret=-(1/(2pi r)) d_r G_3^ret",
        "retarded_step_kernel_for_t_gt_r":str(green_4D_step),
        "ramp_4spatial_wave_PDE_away_from_source":"PASS",
        "retarded_no_signal_before_ambient_null_front":True,
        "static_point_source_asymptote":"1/(4*pi^2*r^2)"}

def audit(radius=1., pulse_duration=.25):
    if not all(math.isfinite(x) for x in (radius,pulse_duration)):
        raise ValueError("Finite physical parameters required")
    if radius<=0 or pulse_duration<=0 or pulse_duration>=2*(PI-2)*radius:
        raise ValueError("Pulse support must allow an early common-detector observation")
    symbolic=symbolic_audit()
    chord=2*radius
    arc=PI*radius
    detection=chord+pulse_duration/2
    response=retarded_receiver(detection,chord,pulse_duration)
    assert chord<detection<arc
    assert response>0
    assert retarded_receiver(chord,chord,pulse_duration)==0
    assert retarded_receiver(chord-0.05*radius,chord,pulse_duration)==0
    assert retarded_receiver(detection,chord,pulse_duration,detector=0.5)==response/2
    # finite receiver location r=d>0 and finite clock, but distributional
    # ideal point source makes energy divergent at emitter. Do not promote.
    return dict(symbolic,**{
       "status":"PASS classical 5D massless TEST scalar retarded emitter-receiver; no graviton or experiment",
       "ambient_metric":"Minkowski_4+1; same source/detector as original cylinder source",
       "source":"brane-localized ideal point pulse q(t)=t_+-2(t-tau)_++(t-2tau)_+",
       "detector":"linear scalar pickup lambda_det phi at opposite brane site",
       "radius":radius,"pulse_duration":pulse_duration,
       "bulk_null_first_front_t":chord,
       "brane_restricted_photon_first_front_t":arc,
       "same_receiver_earlier_test_t":detection,
       "receiver_response_at_t":response,
       "signal_prior_to_brane_light":True,
       "ambient_5D_null_causality_respected":True,
       "positive_receiver_response_requires_source":True,
       "ideal_point_source_total_energy_finite":False,
       "bulk_field_is_real_graviton":False,
       "Einstein_Israel_backreaction_of_this_scalar_model":False,
       "observed_experiment":False,
       "wave_receiver_response_model_not_device":True
    })

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--radius",type=float,default=1.)
    ap.add_argument("--pulse-duration",type=float,default=.25)
    ap.add_argument("--out")
    a=ap.parse_args()
    result=audit(a.radius,a.pulse_duration)
    body=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if a.out:open(a.out,"w",encoding="utf-8").write(body)
    print(body)
if __name__=="__main__":main()
