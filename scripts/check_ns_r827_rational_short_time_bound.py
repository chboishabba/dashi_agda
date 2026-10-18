#!/usr/bin/env python3
"""R827 finite-ODE short-time rational bound for the existing R823 witness.

This bounds the *independent Fourier evaluator* of the R823/R815 rate, not
yet an Agda-R408 same-object identification or a Clay result. The finite
26-mode polynomial ODE is locally solvable by standard ODE theory.
All constants are exact integers/fractions; no floating-point simulation.
"""
from fractions import Fraction as Q
import json

n, M, U0 = 26, 8, 4
# For radius-one nonzero k: component norms of Leray P_k <= 4;
# of helical H_k^+/- = (P_k +/- i k cross / |k|)/2 <= 3.
P, H, cross, dot, laplacian = 4, 3, 2, 3, 3
# f_k = -i P_k sum_{p+q=k} (q dot u_p)u_q.
F = P*n*dot*M*M
FL = P*n*2*dot*M
ODE = F + laplacian*M
hu, huL, hf, hfL = H*M, H, H*F, H*FL
# mixed = sum H+(u_p) cross H-(u_q).
mixed = n*cross*hu*hu
mixedL = n*cross*2*hu*huL
# comm = sum [H+(f_p) cross H-(u_q) - H-(f_p) cross H+(u_q)].
comm = n*2*cross*hf*hu
commL = n*2*cross*(hfL*hu+hf*huL)
# W = 2 Re sum_k <mixed_k,comm_k>; 3 components per mode.
WL = 2*n*3*(mixedL*comm + mixed*commL)
# Pcrit = 2 sum Re <u_k,f_k>; dcrit = sum |k|^2 |u_k|^2.
prodL = 2*n*3*(F+M*FL)
dissL = n*3*laplacian*2*M
# R815/R823 rate = 6*(12 W - Pcrit + dcrit) at nu=delta=1.
rateL = 6*(12*WL+prodL+dissL)
# Exact seed rate from check_ns_r823_exact_sparse_reserve_witness.py
# is -19800-4248 sqrt(2), hence < -19800.
margin = 19800
# Bootstrap solution in ||u||_infty <= 8, starting <=4;
# |u(t)-u(0)| <= ODE*t. Select positive explicit interval.
ballT = Q(M-U0,2*ODE)
rateT = Q(margin,2*rateL*ODE)
T = min(ballT,rateT)
assert 0 < T and U0+ODE*T < M
assert rateL*ODE*T <= Q(margin,2)
assert -margin+rateL*ODE*T <= -9900
# Continuous rate <= -9900 on [0,T], hence integral < -9900 T < 0.
assert -9900*T < 0
if __name__ == "__main__":
    print(json.dumps({
        "schema":"ns_r827_rational_short_time_bound_v1",
        "modes":n,"initial_component_bound":U0,"bootstrap_bound":M,
        "ode_component_bound":ODE,"rate_lipschitz_bound":rateL,
        "ball_horizon":str(ballT),"rate_horizon":str(rateT),
        "chosen_horizon":str(T),"instantaneous_upper_bound":-margin,
        "rate_upper_bound":-9900,"integral_upper_bound":str(-9900*T),
        "same_object_agda_r408_certified":False,
        "agda_kernel_checked":False,"clay_promotion":False
    },indent=2))
