#!/usr/bin/env python3
"""Original 4D L=1 Wilson cubic via EXACT positive rational S3 cubature.

Imports the independently generated degree-7 rational 120-node design
certificate and original six-commutator sparse quaternion polynomial.
Tensorizes the exact one-link orbit rule over the four original links.
No Haar oracle, trig, algebraic root, Monte Carlo or float is used.
"""
import runpy
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as F
from math import prod
BASE=Path(__file__).resolve().parent
sphere=runpy.run_path(str(BASE/"check_ym_s3_exact_rational_orbit_designs_20261117.py"))
orig=runpy.run_path(str(BASE/"check_ym_original_L1_cubic_sparse_pochhammer_20261117.py"))
design=sphere["C"][7]
H=sphere["H"]
orbital=sphere["orbit_average"]
D=orig["D"]; mul=orig["mul"];ZERO=orig["ZERO"]

@lru_cache(None)
def one_link_cubature(e):
 e4=(0,)+e
 result=sum((w*orbital(q,e4) for q,w in design),F(0))
 assert result==H(e4),(e4,result,H(e4))
 return result

def tensor_integral(poly):
 return sum((coeff*prod(one_link_cubature(e[3*j:3*j+3])
                        for j in range(4))
             for e,coeff in poly.items()),F(0))
P={ZERO:1}
expected=(F(1),F(9,2),F(187,8),F(6445,48))
for k in range(4):
 value=tensor_integral(P)
 assert value==expected[k],(k,value,expected[k])
 print(f"original L1 order={k}, polynomial_terms={len(P)}, H[D^{k}]={value}")
 if k<3:P=mul(P,D)
print(f"YM_ORIGINAL_L1_RATIONAL_DESIGN_WELD_PASS: "
      f"{one_link_cubature.cache_info().misses} distinct per-link "
      "monomial certificates plus all four Wilson moments")
