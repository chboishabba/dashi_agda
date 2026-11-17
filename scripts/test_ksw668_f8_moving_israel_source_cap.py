#!/usr/bin/env python3
"""All-velocity original moving-Israel source SOS polynomial certificate.

Exact Fraction proof controls. No numerical evolution, Agda order
kernel proof or physical Weyl convergence claim.
"""
from fractions import Fraction as F
import random

def main():
    rng=random.Random(6683902);count=0
    for _ in range(750):
        v=F(-rng.randint(1,9),10)
        p=F(rng.randint(-15,15),rng.randint(1,9))
        m=F(rng.randint(-15,15),rng.randint(1,9))
        src=F(rng.randint(-15,15),rng.randint(1,9))
        target=F(rng.randint(-15,15),rng.randint(1,9))
        a=1+v;b=1-v
        lower=-a*p*p/2-b*(m-target)**2/2+b*target**2/2
        certificate=(a*(v*p-src)**2-b*src**2
                     -b*b*v*(m-target)**2/2
                     +v*(b*target-a*p+2*src)
                       *(b*target+a*p-2*src)/2)
        assert b*v*lower==certificate
        count+=1
        target=(a*p-2*src)/b
        lower=-a*p*p/2-b*(m-target)**2/2+b*target**2/2
        squares=(a*v/b*(p-src/v)**2
                 -b*(m-target)**2/2-src**2/v)
        assert lower==squares and lower<=-src**2/v
        count+=1
    assert -F(9,16)==-F(3,5)*F(15,16)
    print(f"{count}/{count} exact all-velocity original Israel SOS/cap checks PASS")

if __name__=="__main__": main()
