#!/usr/bin/env python3
"""Exact integer continuations of DASHI pointed-sheet/C3/S3 dimension seam.

D(n)=(n+1)*3^n+6*n is a DECLARED structural extension of n=9:
(n+1) chart markers, ternary n-site sheet, six-by-n coarse modes.
For n=3^d sites, coarse 6n=1+(1+2*(3n-1)): one invariant,
one seam, two copies of the punctured 3*n-position cube.
This is not a proved topological pants gluing, nor a unique possible
continuation of the 196884 Monster coefficient.

C3: q=(n+1)*3^(n-1) free regular orbits plus 6n fixed points.
S3: selected-trit inversion plus coarse punctured-pair swap gives
multiplicities trivial=q+3n+1, sign=3n-1, standard2d=q.
Self-indexed nine-valued functional tower A_(k+1)=9^A_k and
tensor powers 196884^k are separate operations.
"""
from decimal import Decimal,localcontext
from math import lgamma,log
import json

def sheet(n):
    if type(n)!=int or not 1<=n<=10000:
        raise ValueError("bounded positive site count required")
    q=(n+1)*3**(n-1)
    fine=3*q;coarse=6*n;dim=fine+coarse
    m0=q+3*n+1; msign=3*n-1; mstandard=q
    assert m0+msign+2*mstandard==dim
    assert m0+msign-mstandard==coarse
    assert m0-msign==q+2
    return dict(n=n,dimension=dim,fine=fine,coarse=coarse,
                C3_regular_blocks=q,C3_traces=[dim,coarse,coarse],
                S3_irreps=[m0,msign,mstandard],
                S3_reflection_trace=q+2,
                coarse_seam_plus_two_punctured_count_matches=(
                    6*n==1+1+2*(3*n-1)))

def tensor(k):
    if type(k)!=int or not 1<=k<=12:
        raise ValueError("tensor depth invalid")
    d=196884**k; t=54**k
    assert (d-t)%3==0
    return dict(k=k,dimension=d,C3_generator_trace=t,
       C3_irreps=[(d+2*t)//3,(d-t)//3,(d-t)//3])

def self_indexed():
    a2=9**9
    with localcontext() as ctx:
        ctx.prec=60
        logd=Decimal(a2)*Decimal(3).log10()+Decimal(a2+1).log10()
        loga3=Decimal(a2)*Decimal(9).log10()
    return dict(A0=1,A1=9,A2=a2,
      approximate_extended_dimension_D_A2_decimal_digits=int(logd)+1,
      A3_decimal_digits=int(loga3)+1,
      A3="9^(9^9)",A4="9^(9^(9^9))",
      independent_recursion="A_(k+1)=9^A_k")

def receipt():
    assert sheet(9)["dimension"]==196884
    assert sheet(9)["C3_regular_blocks"]==65610
    assert sheet(9)["S3_irreps"]==[65638,26,65610]
    return dict(schema=1,
        sheet_continuation=[sheet(n) for n in (3,9,10,11,12,18,27,54,81)],
        tensor_continuation=[tensor(k) for k in (1,2,3,4)],
        self_indexed=self_indexed(),
        factorial_196830_digits=int(lgamma(196831)/log(10))+1,
        extension_is_uniquely_forced=False,
        same_as_original_Monster_Griess_action=False)

if __name__=="__main__":
    print(json.dumps(receipt(),sort_keys=True,indent=2))
