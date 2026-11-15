#!/usr/bin/env python3
"""D2: exact positive-tension scalar-winding STABILISED TEST brane in flat 5D.

Worldvolume Rt x S1(R) x R2, h=diag(-1,R²,1,1).
Brane action -integral sqrt(-h)[T+(f²/2)*h^ab*d_a chi*d_b chi].
With compact-scalar winding chi=n*theta (n positive integer),
E(R)=2*pi*T*R+pi*f²*n²/R per unit noncompact uv area.
Minimum R*=f*n/sqrt(2*T); radial shape equation S^{ab}K_ab=0.
Stress tensor obeys NEC in worldvolume null directions, and a
5D massless scalar F(t+X) solves free box5 F=0 along the ambient chord.

ALL THESE ARE PROBE-LIMIT EQUATIONS. No 5D Einstein-Israel junction,
backreaction, localized emission, physical gravitational wave, global
all-mode stability or experimental receiver is supplied. Do not call
a positive brane energy a source of "free energy" or violate 5D causality.
This is an original illustrative test model, NOT a reproduction of
Caldwell–Langlois (DOI 10.1016/S0370-2693(01)00631-1).
"""
import json
import sympy as s

def audit():
    R,T,f,n=s.symbols("R T f n",positive=True,real=True)
    h=s.diag(-1,R**2,1,1)
    inv=s.diag(-1,R**-2,1,1)
    dchi=s.Matrix([0,n,0,0])
    grad2=s.simplify((dchi.T*inv*dchi)[0])
    S=(-T*h+f**2*(dchi*dchi.T-s.Rational(1,2)*h*grad2)).applyfunc(s.simplify)
    energy=2*s.pi*T*R+s.pi*f**2*n**2/R
    Rstar=f*n/s.sqrt(2*T)
    assert s.simplify(s.diff(energy,R).subs(R,Rstar))==0
    radial_stiffness=s.simplify(s.diff(energy,R,2).subs(R,Rstar))
    assert radial_stiffness.is_positive
    assert s.simplify(S[1,1].subs(R,Rstar))==0
    extrinsic_K_theta_theta=-R
    shape=s.simplify(inv[1,1]*inv[1,1]*S[1,1]*extrinsic_K_theta_theta)
    assert s.simplify(shape.subs(R,Rstar))==0
    null=s.Matrix([1,1/R,0,0])
    assert s.simplify((null.T*h*null)[0])==0
    NEC=s.simplify((null.T*S*null)[0])
    assert s.simplify(NEC-f**2*n**2/R**2)==0
    t,X,w=s.symbols("t X w",real=True)
    pulse=s.exp(-((t+X-R)/w)**2)
    assert s.simplify(-s.diff(pulse,t,2)+s.diff(pulse,X,2))==0
    assert s.simplify(Rstar.subs({T:2,f:2,n:1}))==1
    assert s.simplify(radial_stiffness.subs({T:2,f:2,n:1}))==8*s.pi
    assert s.simplify(energy.subs({T:2,f:2,n:1,R:1}))==8*s.pi
    return {
      "status":"PASS exact positive-tension+winding scalar equilibrium in 5D flat TEST brane",
      "original_source_type":"new illustrative probe-worldvolume model, NOT original AdS braneworld cosmology",
      "worldvolume_metric":"diag(-1,R²,1,1)",
      "source_action":"-integral sqrt(-h)*(T+f²/2*h^ab*partial_a_chi*partial_b_chi)",
      "winding":"chi=n theta, n positive integer",
      "energy_per_uv_area":str(energy),
      "stationary_radius":str(Rstar),
      "radial_shape_stress":str(S[1,1]),
      "extrinsic_radial_shape_equation":str(shape),
      "null_energy_contraction":str(NEC),
      "uniform_radial_stable":True,
      "example_T2_f2_n1_radius":1,
      "example_min_energy_per_uv_area":"8*pi",
      "bulk_massless_scalar_pulse_equation":"PASS; F(t+X) exact solution",
      "full_brane_perturbation_stability":False,
      "5D_gravitating_Einstein_Israel_solution":False,
      "localized_source_receiver_coupling":False,
      "physical_graviton_signal_measured":False,
      "real_free_energy_or_superluminal":False
    }

if __name__=="__main__":
    print(json.dumps(audit(),sort_keys=True,indent=2))
