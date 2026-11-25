"""Exact cyclic solver and signed phase reconstruction controls."""
from monster3b_char0_orbit_weld import *

# 2D irreducible source fixture; exact nonorthogonal change of chart.
D=mat([[K.one,K.zero],[K.zero,-K.one]])
E=mat([[K.zero,K.one],[K.one,K.zero]])
X=mat([[K.one,Z+1],[K.zero,K.one]])
S={'D':D,'E':E};L={g:X*a*X.inv() for g,a in S.items()}
F,Fi=exact_orbit(S,L,['','E'],0)
require(F*Fi==eye(2) and Fi*F==eye(2),'exact inverse')
require(coordinates(F,F*D)==D,'exact coordinate closure')
try:exact_orbit(S,{'D':D,'E':eye(2)},['','E'],0)
except Exception:pass
else:raise ValueError('bad generator accepted')
print({'exact_generator_equations':4,'two_sided_inverse':2,'coordinate_closure':1,'negative_control':1})
