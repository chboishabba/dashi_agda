#!/usr/bin/env python3
"""Rigorous a posteriori finite-grid versus continuum λ1 error enclosure.

For the selected m=3 Gielis domain, two independent, proven bounds:
 * continuum Dirichlet:   C_lo=224/55 < λ_c < C_hi=1273/264
   (Faber-Krahn/Bessel + independent H0¹ Rayleigh test).
 * exact finite 5-point FD: F_lo <= λ_h <= F_hi
   (rational positive-vector ground-state / Rayleigh certificate).

For ALL λ_c and λ_h consistent with these original theorem inputs,
   |λ_h - λ_c| < max(C_hi-F_lo, F_hi-C_lo, 0),
strict when both continuum bounds strict.
No estimate of the convergence RATE is being claimed.
No evaluation of a numerical eigenvalue is trusted as a proof:
scipy proposes only the positive vector; final bounds are exact Fraction.

This is an actual quantitative finite-grid continuum error bound with
explicit rational end points, albeit loose; sharper certified O(h^p)
rates still need a dedicated interpolation/stability theorem.

Other m are rejected: the 1273/264 upper bound is specific to m=3.
"""
from __future__ import annotations
from fractions import Fraction as F
import argparse,json
from gielis_raster_fd_positivity_certificate import certify
from gielis_physical_spectral_si import LOW,HIGH

def exact_error_enclosure(finite_lower,finite_upper,continuum_lower=LOW,continuum_upper=HIGH):
    fl=F(str(finite_lower));fu=F(str(finite_upper))
    cl=F(str(continuum_lower));cu=F(str(continuum_upper))
    if not (0<fl<=fu and 0<cl<cu):
        raise ValueError("positive, ordered independently certified intervals required")
    e=max(F(0),cu-fl,fu-cl)
    # Lower endpoint of absolute error; intervals overlap -> 0.
    gap=max(F(0),fl-cu,cl-fu)
    assert gap<=e
    return {
      "continuum_lower_strict":str(cl),
      "continuum_upper_strict":str(cu),
      "finite_lower_closed":str(fl),
      "finite_upper_closed":str(fu),
      "absolute_error_rational_strict_upper":str(e),
      "absolute_error_upper_decimal":float(e),
      "absolute_error_rational_lower":str(gap),
      "relative_error_rational_strict_upper":str(e/cl),
      "continuum_interval_width":str(cu-cl),
      "finite_interval_width":str(fu-fl),
      "valid_for_all_eigenvalues_within_independent_intervals":True,
      "finite_to_continuum_error_quantitatively_bounded":True,
      "mesh_order_rate_Oh_power_certified":False,
      "rates_not_inferred_from_two_meshes":True,
    }

def receipt(m=3,n=41,scale=10**15):
    if m!=3:raise ValueError("m=3 continuum upper is required; other modes not proved")
    original=certify(m,n,scale)
    c=exact_error_enclosure(original["rational_lower"],original["rational_upper"])
    return {
      "status":"certified_a_posteriori_finite_grid_continuum_lambda1_error",
      "selected_Gielis_mode":m,
      "original_exact_grid":n,
      "interior_nodes":original["interior_nodes"],
      "finite_matrix_source":"original exact rational Gielis FD positive-vector theorem",
      "continuum_source":"original E15 Rayleigh upper and E35 Faber-Krahn/Bessel lower",
      "same_selected_unshrunken_raster_domain":True,
      "no_binary64_membership":original["exact_unshrunken_domain_rational_predicate"],
      "theorem":"max(C_upper-F_lower,F_upper-C_lower,0)",
      "interval_certificate":c,
      "actual_Gielis_numerical_eigenvalue_used_as_proof":False,
      "native_Agda_full_continuum_error_theorem":False,
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--mode",type=int,default=3)
    p.add_argument("--grid",type=int,default=41)
    p.add_argument("--scale",type=int,default=10**15)
    args=p.parse_args()
    print(json.dumps(receipt(args.mode,args.grid,args.scale),sort_keys=True,indent=2))
if __name__=="__main__":main()
