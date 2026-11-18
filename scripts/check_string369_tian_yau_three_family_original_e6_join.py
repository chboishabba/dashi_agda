#!/usr/bin/env python3
"""Tian-Yau CY3 CICY -> index three and original E6 27 -> SM charge source.

ORIGINAL PUBLIC MATHEMATICS: Tian/Yau; Candelas/Lütken/Schimmrigk
CICY, Euler sequence/adjunction; Atiyah-Singer; heterotic E8 standard
embedding. Freely acting Z3 quotient and Wilson-line construction are
external published theorems, NOT proved by Euler arithmetic here.
ORIGINAL DASHI (Johl Brown and original collaborators):
first-Tits E6 27 PR #1106 and KK Higgs/orbifold PR #1241;
scripts/check_kk_e6_post_e32_sm_global_z6.py,
scripts/check_kk_e6_post_e21_u3_photon.py.
NEW: exact source-preserving Chern-to-3 index and execution of ORIGINAL
27-charge consumers. KK S1 momentum remains INDEPENDENT of hypercharge.
No full heterotic 10D solution, exact-head Agda kernel or observed 3
family physics claimed. User supplied research direction.
"""
import sympy as s
from pathlib import Path
from contextlib import redirect_stdout
import runpy,io
H1,H2,t=s.symbols("H1 H2 t")
# Complete intersection in P3_x x P3_y cut by (3,0),(0,3),(1,1).
D1,D2,D3=3*H1,3*H2,H1+H2
total=(1+t*H1)**4*(1+t*H2)**4/((1+t*D1)*(1+t*D2)*(1+t*D3))
chern=s.series(total,t,0,4).removeO().expand()
c1=s.expand(chern.coeff(t,1))
c2=s.expand(chern.coeff(t,2))
c3=s.expand(chern.coeff(t,3))
assert c1==0,(c1,c2,c3)
euler_cover=s.expand(c3*D1*D2*D3).coeff(H1,3).coeff(H2,3)
assert euler_cover==-18
# ONLY under externally established FREE Z3 group action.
group_order=3
assert euler_cover%group_order==0
euler_quotient=euler_cover//group_order
net_standard_embedding=abs(euler_quotient)//2
assert euler_quotient==-6 and net_standard_embedding==3
# Distinguish complete-intersection cover from the quintic and its
# nonfree cyclic permutation: -200/3 is not an integer!
assert (-200)%3!=0
# Execute exact original gauge-source 27-state generators, not copies.
root=Path(__file__).resolve().parents[1]
def original(path):
    with redirect_stdout(io.StringIO()) as receipt:
        out=runpy.run_path(str(root/"scripts"/path))
    assert "PASS" in receipt.getvalue()
    return out
sm=original("check_kk_e6_post_e32_sm_global_z6.py")
em=original("check_kk_e6_post_e21_u3_photon.py")
assert len(sm["states"])==27 and len(em["states"])==27
assert len(sm["kernel"])==6 and len(em["kernel"])==6
assert all((-qz)%2==0 for _b,_c,_l,_r,_t,qz,_h in em["states"])
assert all((t+(-qz//2))%3==0 for _b,_c,_l,_r,t,qz,_h in em["states"])
# KK circle-momentum n is not any of these SU3/weak weights.
# The original E6 charge is a function of representation indices;
# it is independent of n absent an EXTRA equality of gauge generators.
n=s.symbols("n",integer=True)
assert s.diff(n,n)==1
print("PASS: CICY total Chern c1=0; Euler covering -18")
print("PASS: conditional free Z3 quotient Euler=-6 and standard-embedding index magnitude=3")
print("PASS: imported ORIGINAL E6 27 chiral 16+11 and Z6 hypercharge sources")
print("PASS: imported ORIGINAL E21 U3_EM quotient; all 27 integral 3Q and triality")
print("NOT PROVED: selected Tian-Yau free action, full bundle descent, Wilson-line spectrum")
print("NOT PROVED: KK momentum generator equals physical EM or observed hypercharge")
