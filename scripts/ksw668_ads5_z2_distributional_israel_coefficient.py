#!/usr/bin/env python3
"""D2/B1: Z2 Gaussian-normal distributional Israel jump: ALL 16 same-source components.

SOURCE: W. Israel, Nuovo Cimento B 44 (1966) 1–14,
doi:10.1007/BF02710419; Caldwell-Langlois 2001
doi:10.1016/S0370-2693(01)00631-1 moving AdS5 FRW brane.

The earlier original source script independently verified *one-sided*
K^a_b and S^a_b, hence the algebraic Z2 Israel relation. This
complements it with the distributional Gaussian-normal coefficient.

Near a Z2 brane, Gaussian normal bulk metric has
   g_ab(y)=h_ab + 2 |y| K^+_ab + O(y²);
   g_yy=+1, g_ay=0.
Therefore ∂_y²|y| = 2 delta(y), the singular Einstein coefficient is
   (G_ab)^sing = -([K_ab] - h_ab[K]) delta(y)
                = -2(K^+_ab-h_ab K^+) delta(y).
Exact 5D Einstein source equation requires
   -2(K^+_ab-h_ab K^+) = kappa5² S_ab, kappa5²=6.
All 16 components and the original source/moving-brane clock are tested.
The unbounded, global O(y²) data and bulk glue are NOT derived merely
from this local distributional coefficient; a full functional-analytic
distributional Agda proof remains OPEN. Z2 normal reflection is not
equivalent to the unrelated Z3 trialectic, Fourier integer lattice,
or Monster actions in the repository.
"""
import sympy as s
import json

def audit():
    t=s.symbols("t",positive=True,real=True)
    A=s.sqrt(1+1/t**2)
    h=s.diag(-1,t**2,t**2,t**2)
    K_mixed=s.diag(-1/A,-A,-A,-A)
    K_cov=(h*K_mixed).applyfunc(s.simplify)
    K_trace=s.simplify(s.trace(K_mixed))
    rho=A-1
    p=s.simplify(-rho-s.diff(rho,t)/(3/t))
    sigma=s.Integer(1)
    S_mixed=s.diag(-(rho+sigma),p-sigma,p-sigma,p-sigma)
    S_cov=(h*S_mixed).applyfunc(s.simplify)
    kappa=s.Integer(6)
    jump_minus_trace=(2*(K_cov-h*K_trace)).applyfunc(s.simplify)
    coeff_G_sing=(-jump_minus_trace).applyfunc(s.simplify)
    expected=(kappa*S_cov).applyfunc(s.simplify)
    assert coeff_G_sing==expected
    assert all(s.simplify(coeff_G_sing[i,j]-expected[i,j])==0
               for i in range(4) for j in range(4))
    # Time slice with rational square root =5/4:
    t0=s.Rational(4,3)
    at0=coeff_G_sing.subs(t,t0).applyfunc(s.simplify)
    rhs0=expected.subs(t,t0).applyfunc(s.simplify)
    assert at0==rhs0
    assert list(at0.diagonal())==[s.Rational(15,2),
                                s.Rational(-176,15),
                                s.Rational(-176,15),
                                s.Rational(-176,15)]
    # The sign -2(K-hK) = kappa S, versus jump 2(K-hK) = -kappa S.
    # Symbolically ∂y²|y|=2delta(y); non-smooth at y=0.
    y=s.symbols("y",real=True)
    even=s.Abs(y)
    # Proof of jump is the difference of one-sided *first* derivatives.
    assert s.diff(y,y)==1
    derivative_plus=s.diff(y,y)
    derivative_minus=s.diff(-y,y)
    assert derivative_plus-derivative_minus==2
    assert s.simplify(s.trace(K_mixed)-s.trace(S_mixed))==0
    return {
      "status":"PASS 5D Z2 Gaussian-normal distributional Einstein coefficient all 16 components",
      "original_Israel_DOI":"10.1007/BF02710419",
      "original_AdS_brane_DOI":"10.1016/S0370-2693(01)00631-1",
      "dimension":"5D bulk, 4D timelike brane",
      "Z2_jump":"K^-_ab=-K^+_ab",
      "distribution_identity":"d_y²|y|=2 delta(y)",
      "singular_Einstein_tensor_coefficient":"-2(K_ab-h_ab K)=kappa5² S_ab",
      "same_source_tauextrinsic":True,
      "all_16_original_component_identities":True,
      "selected_t4over3_Gsing_diagonal":[str(x) for x in at0.diagonal()],
      "selected_t4over3_S_kappa_diagonal":[str(x) for x in rhs0.diagonal()],
      "bulk_metric_global_distribution_constructed":False,
      "time_dependent_TT_graviton_BC_solved":False,
      "physical_receiver_or_observed":False,
      "equates_Z2_junction_to_Z3_or_3+1_Monster":False,
      "Agda_distributional_metric_kernel_accepted":False
    }

if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
