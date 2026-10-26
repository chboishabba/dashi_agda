#!/usr/bin/env python3
"""Exact character-norm and cyclic restriction receipt, not a Monster-module proof."""
from fractions import Fraction
import json
n=6; d=3**n; h=3**(2*n+1)
assert Fraction(3*d*d,h)==1
assert 3**(2*n)+2*d*d==h
monster=(65663,65610,65610)
pointed=(65610,65610,65610)
delta=tuple(x-y for x,y in zip(monster,pointed))
assert delta==(53,0,0)
assert sum(monster)==196883 and sum(pointed)==196830
receipt=dict(degree=d,heisenberg_order=h,norm_square='1',linear_irreducibles=3**12,nonlinear_irreducibles=2,monster_C3=monster,pointed_C3=pointed,residual_C3=delta,monster_selected_3B_trace=53,pointed_selected_C3_trace=0,qualification='abstract complex C3 comparison only; actual E and normalizer action not proved')
print(json.dumps(receipt,indent=2))
