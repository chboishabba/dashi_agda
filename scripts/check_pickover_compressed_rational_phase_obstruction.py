#!/usr/bin/env python3
"""Exact modular surrogate for the Pickover exponent; NOT the real sine sign."""
from math import factorial

def surrogate(m,a,b):
    """For rational alpha=a/b, return b*99**m mod (2*a)."""
    return (b*pow(99,m,2*a))%(2*a)

def main():
    for m in (1,2,6,24):
        for a,b in ((22,7),(355,113)):
            assert surrogate(m,a,b)==(b*99**m)%(2*a)
    m=factorial(9999)
    assert m.bit_length()>100000
    print("Exact rational surrogate residue verified.")
    print("Exponent bit length:",m.bit_length())
    print("No certified irrational phase; sign not evaluated.")
if __name__=="__main__":
    main()
