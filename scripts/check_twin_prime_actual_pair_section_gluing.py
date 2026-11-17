#!/usr/bin/env python3
"""Exact-integer two-endpoint section gluing and single-marginal no-go."""
def shifted(a):
    return sum(a[n]*a[n+2] for n in range(len(a)-2))
def verify():
    a=[1,0,1,0,1,0,1,0]
    b=[1,1,1,1,0,0,0,0]
    assert sorted(a)==sorted(b)
    assert sum(a)==sum(b)
    assert shifted(a)==3 and shifted(b)==2
    # Exact overlapping sections agree on BOTH actual endpoint readings.
    c=list(range(19))
    left={n:(c[n],c[n+2]) for n in range(1,9)}
    right={n:(c[n],c[n+2]) for n in range(5,13)}
    for n in set(left)&set(right):
        assert left[n]==right[n]
        assert left[n][0]*left[n][1]==right[n][0]*right[n][1]
    print('PASS: same one-point multiset/mean, different lag-two correlation')
    print('PASS: exact endpoint overlap gluing for 4 common section indices')
if __name__=='__main__': verify()
