#!/usr/bin/env python3
"""D4h homogeneous invariant dimensions: independent exact Molien audit.

Classical finite reflection-group result, implemented as a finite
combinatorial certificate; not an Agda kernel proof nor a diffraction test.
For degree d, invariant polynomials have monomial orbit representatives
(x²y²)^b (x²+y²)^a (z²)^c with 2a+4b+2c=d.
"""
from fractions import Fraction
def predicted(d):
    return sum(1 for a in range(d//2+1)
               for b in range(d//4+1)
               for c in range(d//2+1) if 2*a+4*b+2*c==d)
def independently_count(d):
    # Signs in x,y,z require all individual exponents even;
    # x<->y then identifies exponent pairs. Count orbits directly.
    triples=[(i,j,d-i-j) for i in range(d+1) for j in range(d-i+1)
             if i%2==j%2==(d-i-j)%2==0]
    return len({(min(i,j),max(i,j),k) for i,j,k in triples})
def check():
    for d in range(21):
        assert independently_count(d)==predicted(d), d
    assert [predicted(d) for d in range(0,9)]==[1,0,2,0,4,0,6,0,9]
    print("PASS: D4h invariant Hilbert dimensions, degrees 0..20; quartic dim 4.")
if __name__=="__main__":check()
