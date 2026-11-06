#!/usr/bin/env python3
"""Exact rational sector-sampling spectral geometry certificate.

For r_m(theta)=2/sqrt(3+cos(m*theta)), a nearest-sector sample on
N angular sectors has |r_N-r| <= m*pi/(2*sqrt(2)*N)
< 55m/(49N), using pi<22/7 and sqrt(2)>7/5.
Since r>=1, (1-e)Omega subset Omega_N subset (1+e)Omega.
Dirichlet domain monotonicity and dilation scaling imply for ALL k:
 (1+e)^(-2) <= lambda_k(Omega_N)/lambda_k(Omega) <= (1-e)^(-2).
This is a certified continuum geometry-discretisation bound, NOT a
certification of the 41/61-node Cartesian FD eigensolver.
"""
from __future__ import annotations
from fractions import Fraction
import argparse, json, math

def certificate(m:int,sectors:int)->dict:
    if type(m) is not int or type(sectors) is not int or m<=0 or sectors<=0:
        raise ValueError("positive integer mode and sectors required")
    eps=Fraction(55*m,49*sectors)
    if eps>=1: raise ValueError("55*m must be < 49*sectors")
    lower=(1+eps)**-2
    upper=(1-eps)**-2
    error=max(1-lower,upper-1)
    def frac(x):return str(x.numerator)+"/"+str(x.denominator)
    return {
        "mode":m,"sector_count":sectors,
        "rigorous_radial_relative_error_upper":frac(eps),
        "spectrum_lower_ratio":frac(lower),
        "spectrum_upper_ratio":frac(upper),
        "relative_eigenvalue_error_upper":frac(error),
        "relative_error_bound_decimal":float(error),
        "all_dirichlet_eigenvalues_continuum_sector_domain":True,
        "certified_cartesian_fd_eigensolver_error":False,
        "hypothesis":"nearest angular sample; sectorwise-constant radial domain",
        "proof":"r>=1; |r'|<=m/(2sqrt(2)); pi<22/7; sqrt2>7/5; domain inclusion + scaling",
    }

def minimal_sector_count(m:int,relative_target:Fraction,max_sectors=1000000)->int:
    if relative_target<=0:raise ValueError("relative target must be positive")
    for n in range(max(1,(55*m)//49+1),max_sectors+1):
        c=certificate(m,n)
        if Fraction(c["relative_eigenvalue_error_upper"])<=relative_target:return n
    raise ValueError("target not achieved within sector budget")

def assert_numerical_geometry_examples(m:int,n:int):
    # Supplementary sanity check; NOT the source of the rigorous result.
    values=[2/math.sqrt(3+math.cos(m*2*math.pi*j/n)) for j in range(n)]
    e=float(Fraction(55*m,49*n))
    for j in range(n):
        for sub in range(17):
            angle=2*math.pi*(j+(sub-8)/16)/n
            r=2/math.sqrt(3+math.cos(m*angle))
            assert (1-e)*r-1e-12 < values[j] < (1+e)*r+1e-12

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--m",type=int,default=9)
    p.add_argument("--sectors",type=int,default=2048)
    p.add_argument("--target-percent",type=float,default=1.)
    p.add_argument("--output")
    a=p.parse_args()
    out=certificate(a.m,a.sectors)
    out["first_sector_count_for_target"]=minimal_sector_count(a.m,Fraction(str(a.target_percent))/100)
    assert_numerical_geometry_examples(a.m,a.sectors)
    result=json.dumps(out,indent=2,sort_keys=True)
    if a.output:
        from pathlib import Path
        Path(a.output).write_text(result+"\n")
    print(result)

if __name__=="__main__":main()
