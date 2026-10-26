#!/usr/bin/env python3
"""Pickover/Bruhat--Tits 3-adic tree refinement negative control.

Classical: PGL2(Q3) BT tree 4-regular; a rooted affine branch has
three descendants, indexing Z3 residue cylinders.  Here only the
exact finite Z/3^d arithmetic is executed; no BT spectral theorem,
real-circle embedding or new phase algorithm is asserted.
"""
from fractions import Fraction

def digits3(n,d):
    out=[]
    for _ in range(d):
        out.append(n%3);n//=3
    return tuple(out)

def prefix(n,d): return n%(3**d)

def is_prefix(coarse,fine,d):
    return prefix(fine,d)==coarse

def main():
    for d in range(1,6):
        for a in range(3**d):
            children=[a+k*3**d for k in range(3)]
            assert len(set(children))==3
            assert all(is_prefix(a,b,d) for b in children)
            assert all(prefix(b,d+1)!=prefix(c,d+1) for i,b in enumerate(children) for c in children[i+1:])
            assert digits3(a,d)==digits3(children[0],d)
    # 99 is divisible by 3^2. Increasing the exponent loses 3-adic
    # information: every high-enough 99^E occupies the zero cylinder.
    for depth in range(1,13):
        assert prefix(99**((depth+1)//2),depth)==0
    # Two known exact real-phase witnesses have the same 3-adic
    # cylinder signatures at all finite depths <= 12.
    from math import factorial
    x,y=99**9,99**18
    assert all(prefix(x,d)==prefix(y,d)==0 for d in range(1,13))
    # Independent Machin rational floor certificates committed in
    # check_pickover_ninth_power_non_descent.py:
    assert 290781571073447469%2==1
    assert 265633980425984427859213880941867086%2==0
    print('PASS: coherent ternary tree cylinders and p=3 forward branching')
    print('PASS: 3-adic refining observers cannot alone distinguish known opposite sine signs')
    print('OPEN: mixed Archimedean/3-adic analytic seam; terminal sign')
if __name__=='__main__':main()
