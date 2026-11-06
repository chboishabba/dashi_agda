#!/usr/bin/env python3
"""Exact finite-difference Dirichlet quadratic form and vanishing boundary cut.

For the actual n×n Gielis 5-point mask, extend u by zero outside the
selected interior nodes. Then for *every* finite-support grid function,

   4 sum_i u_i² - sum_{i} sum_{j~i,inside} u_i u_j
    = sum_{i,j in Z²}[(u_{i+1,j}-u_{i,j})²
                      +(u_{i,j+1}-u_{i,j})²].

The right side is >= 0, giving discrete energy coercivity up to
normalization. This exact local identity is a starting point for the
usual L2 compactness/Mosco convergence proof. Finite exact checks DO NOT
by themselves prove the continuum limit, and no numerical O(h) rate
is inferred from them.
"""
from __future__ import annotations
import argparse, json
from fractions import Fraction as Q
import numpy as np
import gielis_base369_experiments as G

def mask(m,n):
    if type(m) is not int or m<=0 or type(n) is not int or n<17 or n%2==0:
        raise ValueError("positive m, odd n>=17 required")
    axis=np.linspace(-1.5,1.5,n)
    h=3/(n-1)
    x,y=np.meshgrid(axis,axis,indexing="ij")
    r=G.gielis_radius(np.arctan2(y,x),m)
    inside=np.hypot(x,y)<r-G.raster_boundary_tolerance(h)
    legacy=np.hypot(x,y)<r-1e-12
    return inside, bool(np.array_equal(inside,legacy)), h

def grid_energy(u:dict,n:int):
    def val(i,j):return Q(u.get((i,j),0))
    sq=sum((v*v for v in u.values()),Q(0))
    adj=sum(
        (val(i,j)*(val(i+1,j)+val(i-1,j)+val(i,j+1)+val(i,j-1))
         for i,j in u),Q(0))
    operator=4*sq-adj
    horizontal=sum(
        ((val(i+1,j)-val(i,j))**2
          for i in range(-1,n) for j in range(n)),Q(0))
    vertical=sum(
        ((val(i,j+1)-val(i,j))**2
          for i in range(n) for j in range(-1,n)),Q(0))
    difference=horizontal+vertical
    if operator!=difference:
        raise AssertionError("Dirichlet difference-square identity fails")
    if difference<0:
        raise AssertionError("finite difference energy must be >=0")
    return {
        "operator_energy_integer":str(operator),
        "finite_difference_energy_integer":str(difference),
        "exact_identity":True,
        "discrete_energy_nonnegative":True,
    }

def receipt(m=3,n=41):
    inside,legacy_equal,h=mask(m,n)
    nodes=[(int(i),int(j)) for i,j in np.argwhere(inside)]
    if not nodes: raise ValueError("empty grid")
    families=[
        {(i,j):1 for i,j in nodes},
        {(i,j):(-1)**(i+j) for i,j in nodes},
        {(i,j):(13*i+17*j+3)%23-11 for i,j in nodes},
        {(i,j):i-j for i,j in nodes},
    ]
    checks=[grid_energy(u,n) for u in families]
    delta=G.raster_boundary_tolerance(h)
    assert 0<=delta<=1e-12
    return {
        "status":"exact_discrete_energy_identity_passed",
        "mode":m,"grid":n,"interior_cells":len(nodes),
        "legacy_1e_minus_12_mask_equal_at_selected_n":legacy_equal,
        "boundary_tolerance_m":delta,
        "boundary_tolerance_function":"min(1e-12,(3/(n-1))^2)",
        "boundary_tolerance_limit_zero":True,
        "exact_test_vectors":len(checks),
        "all_difference_squares_nonnegative":all(
            x["discrete_energy_nonnegative"] for x in checks),
        "finite_form_h2_times_A":"4I minus nearest-neighbour adjacency",
        "known_continuum_target":"unshrunken selected Omega_m",
        "liminf_compactness_proof_in_python":False,
        "finite_difference_to_continuum_rate_certified":False,
        "checks":checks,
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--m",type=int,default=3)
    p.add_argument("--grid",type=int,default=41)
    a=p.parse_args()
    print(json.dumps(receipt(a.m,a.grid),indent=2,sort_keys=True))

if __name__=="__main__":main()
