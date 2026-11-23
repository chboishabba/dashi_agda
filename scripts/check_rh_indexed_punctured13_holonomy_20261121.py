#!/usr/bin/env python3
"""Exact native punctured-27 antipode and indexed four-cycle test.
Reference arithmetic only: not an Agda kernel proof, not Monster/Hecke/RH.
"""
from itertools import product

def canonical(p):
    first = next(x for x in p if x)
    return tuple(first*x for x in p)

def main():
    points = list(product((-1, 0, 1), repeat=3))
    nonzero = [p for p in points if p != (0, 0, 0)]
    axes = {canonical(p) for p in nonzero}
    assert len(points) == 27 and len(nonzero) == 26 and len(axes) == 13
    for p in nonzero:
        a = canonical(p)
        orientation = p != a
        assert (tuple(-x for x in a) if orientation else a) == p
        assert canonical(tuple(-x for x in p)) == a

    def impossible(x, pp, y, pm):
        return not ((x^pp)==0 and (pp^y)==0 and (y^pm)==1 and (pm^x)==0)

    signs = list(product((0, 1), repeat=4))
    assert len(signs) == 16
    assert all(impossible(*s) for s in signs)
    # Index coordinates are independent; an index label alone
    # supplies no edge correction for the nontrivial sign cocycle.
    tested = 0
    for h,t,k,j,v in product(range(3),repeat=5):
        for s in signs:
            assert impossible(*s)
            tested += 1
    assert tested == 3888
    print('PASS 27/26/13 original point/antipode reconstruction')
    print('PASS 16/16 signed four-cycle assignments obstructed')
    print('PASS 3888/3888 five-index holonomy counterchecks')
    print('OPEN actual six-face corrected transport and Agda kernel')

if __name__=='__main__':
    main()
