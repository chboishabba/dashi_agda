#!/usr/bin/env python3
"""D1/D2 exact-rational KK signed-fibre causal projection, with negative control.

For the standard spacelike-fibre Kaluza-Klein ansatz:
  ds5² = ds4² + phi²*(dy + A_mu dx_mu)², with phi² >= 0.
If ds5² <= 0, then ds4² <= 0. This does NOT solve 5D Einstein/matter
equations or establish a new operational signal/transport device.
"""
import json
from fractions import Fraction as Q
from itertools import product


def projection(base,phi_squared,fibre_velocity):
    if phi_squared<0:
        raise ValueError("Standard spacelike-fibre metric requires phi² >= 0")
    full=base+phi_squared*fibre_velocity*fibre_velocity
    if full<=0 and not base<=0:
        raise AssertionError("5D causal projected as 4D spacelike")
    return full,base


def check():
    states=0
    causal=0
    for b,r,q in product(range(-4,5),range(0,5),range(-4,5)):
        full,projected=projection(Q(b,2),Q(r,3),Q(q,2))
        states+=1
        if full<=0:
            causal+=1
            assert projected<=0
    assert states==405
    assert causal>0
    # Negative control: a *timelike* fifth dimension changes the theorem.
    fourD=Q(1,1)
    fiveD=fourD-Q(4,1)   # -3 <=0, though 4D +1 >0.
    assert fourD>0 and fiveD<0
    return {
      "status":"PASS exact rational exhaustive finite diagnostic",
      "tested_exact_rational_states":states,
      "states_where_5D_is_causal":causal,
      "all_5D_spacelike_fiber_causal_tangents_project_4D_causal":True,
      "negative_fifth_signature_counterexample":{"4D_interval":str(fourD),
         "5D_interval":str(fiveD),
         "physical_standard_spacelike_fibre":False},
      "original_Agda_proof":"DASHI/Physics/Gravity/KSW668KaluzaKleinSpacelikeFiberCausalExact.agda",
      "physical_5D_Einstein_matter_solution":False,
      "observed_FTL_signal":False,
      "scope":"5D pointwise rational metric ansatz; no dynamical field equations",
    }


if __name__=="__main__":
    print(json.dumps(check(),indent=2))
