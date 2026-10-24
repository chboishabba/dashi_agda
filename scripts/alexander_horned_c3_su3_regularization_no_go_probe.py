#!/usr/bin/env python3
"""Conditional horn holonomy regularity / commutator compression audit.

NEW mathematical finite-depth witness from elementary unitary norms:
 ||[X,Y]-I|| <= 2 ||X-I|| ||Y-I||
 root depth-n bound <= 2^(2^n-1) eps_n^(2^n)
 any fixed nontrivial root with gap d forces
   max_leaf_gap(n) >= 1/2*(2*d)^(1/(2^n)).
If every local representative loop of depth n has length <= ell_n -> 0
and a compatible bounded unitary connection has norm <= M, then
max_leaf_gap(n) <= M ell_n -> 0: contradiction.
The uniform SMALL LOOP GEOMETRY is a distinct, unverified hypothesis
for the proposed physical wild embedding; common-base stems conjugate
loop matrices, preserving these operator norms.

Source: Hatcher, Algebraic Topology Example 2B.2 (binary group tower).
Uses original DASHI FlatFormalDiskHolonomySurface and SUNWilson
owners as cross-program analytic interfaces. No Agda/physics theorem
or geometry certificate is claimed from local floating-point tests.
"""
from math import log,exp
from fractions import Fraction
import numpy as np
from scipy.linalg import eigvals
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"tests"))
from test_neutrino_horned_su3_positive_bridge import residual_target
from test_neutrino_existing_cp_sector_bridge import ZERO

def to_complex(z):
    return float(z[0])+float(z[1])*complex(-.5,np.sqrt(3)/2)
def selected_matrix():
    _,_,A=residual_target()
    return np.array([[to_complex(z) for z in row] for row in A])
def leaf_lower_bound(d,n):
    return .5*exp(log(2*d)/(2**n))
def root_upper_bound_log(eps,n):
    return (2**n-1)*log(2)+(2**n)*log(eps)
def report(depths=(1,2,3,5,8,12)):
    A=selected_matrix()
    d=float(np.linalg.norm(A-np.eye(3),ord=2))
    assert d>1
    rows=[]
    for n in depths:
        bound=leaf_lower_bound(d,n)
        hypothetical_loop_length=2.0**(-n)
        minimal_uniform_connection_norm=bound/hypothetical_loop_length
        rows.append(dict(depth=n,root_gap=d,forced_leaf_gap=bound,
                         illustrative_max_local_loop_length=hypothetical_loop_length,
                         required_local_norm_lower_bound=minimal_uniform_connection_norm))
        assert bound>.5
        assert root_upper_bound_log(hypothetical_loop_length/4,n)<log(d)
    assert all(rows[i]['required_local_norm_lower_bound']<
               rows[i+1]['required_local_norm_lower_bound']
               for i in range(len(rows)-1))
    for row in rows:print(row)
    print("mathematical conditional no-go: PASS")
    print("uniform geometric shrinking loops: ASSUMED, NOT VERIFIED")
    print("analytic bounded connection in compatible local frames: ASSUMED")
    return rows

if __name__=="__main__":report()
