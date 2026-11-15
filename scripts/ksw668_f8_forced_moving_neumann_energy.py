#!/usr/bin/env python3
"""Original a=t AdS5 compact Neumann stress -> finite-energy retarded bound.

With y=z-b(T), W=y chi(y)G/(1-v²) exactly lifts the sourced oblique
Neumann boundary. U=H-W has homogeneous boundary and interior force
f=-L_y W. The boundary-tangent energy satisfies
E'(T)<=gamma E+0.5||f||^2_{z^-3}, gamma=18.89949...
on the original t in [1,2]. This is a mathematical estimate for
smooth compatible IBVP solutions, NOT a Weyl detection.
"""
import json,math
import sympy as s
import mpmath as mp

def symbolic():
    A,B,P,v,w=s.symbols("A B P v w",real=True)
    E0=w*(A*A+B*B+P*P)/2
    EX=w*((A+v*B)**2+(1-v*v)*B*B+P*P)/2
    assert s.expand(EX-(1+v)*E0-
        (-v)*w*((A-B)**2+P*P)/2)==0
    T,y,x=s.symbols('T y x',real=True)
    vel=s.Function('v')(T)
    g=s.Function('G')(T,x)
    cut=s.exp(-y*y/(1-y*y))
    W=y*cut*g/(1-vel*vel)
    wall=(1-vel*vel)*s.diff(W,y)+vel*s.diff(W,T)
    assert s.simplify(wall.subs(y,0)-g)==0
    assert s.simplify(W.subs(y,0))==0
    assert s.simplify(s.diff(W,T).subs(y,0))==0
    return dict(energy_square_completion_exact=True,
       identity='EX-(1+v)E0=(-v) z^-3/2 [(H_T-H_z)^2+|grad H|^2]',
       compact_lift='W=y chi(y)G/(1-v²), chi=exp(-y²/(1-y²)) on [0,1), zero above',
       sourced_moving_wall_lift_exact=True,
       explicit_retarded_4D_or_projected_5D_Weyl_receiver=False)

def bound():
    delta=1-1/math.sqrt(2)
    C=(1+3*math.sqrt(2))/delta
    gamma=C+1
    F=lambda t:mp.asinh(t)-mp.sqrt(1+t*t)/t
    DT=float(F(mp.mpf(2))-F(mp.mpf(1)))
    sample=math.expm1(gamma*DT)/(2*gamma)
    assert delta>0 and C>0 and math.isfinite(sample)
    return dict(original_t_interval='[1,2]',
       original_Poincare_T_duration=DT,
       coercive_factor=delta,growth_constant=C,
       forcing_Gronwall_gamma=gamma,
       zero_initial_smooth_retarded_estimate=
          'E_U(T)<=0.5 integral_T0^T e^(gamma*(T-S)) ||-L_y W(S)||_weighted² dS',
       E_upper_when_weighted_force_norm_below_one=sample,
       finite_weighted_force_for_compact_smooth_G=True,
       nonzero_original_receiver_Weyl_proved=False)

def audit():return dict(symbolic=symbolic(),energy=bound(),
                       experimentally_observed_graviton=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
