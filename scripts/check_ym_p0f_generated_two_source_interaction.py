#!/usr/bin/env python3
"""Independent exact Q regression of three-Z2-character induced RG control.

This is NOT SU(N) physical Wilson, Agda kernel, or proof about the
4-dimensional ultraviolet Wilson RG flow.
"""
from fractions import Fraction as Q
from random import Random

CHAR = {True: Q(1), False: Q(-1)}
SIGNS = (True, False)

def haar2(F):
    return sum((F(x, y) for x in SIGNS for y in SIGNS), Q(0)) / 4

def induced(t):
    assert -1 < t < 1
    def fine(x, y, z):
        return (1 + t*CHAR[x]*CHAR[z])*(1 + t*CHAR[y]*CHAR[z])
    def eff(x, y):
        return sum((fine(x, y, z) for z in SIGNS), Q(0))/2
    return fine, eff

def run():
    rng = Random(144420261113)
    marked = 0
    for t in (Q(1,10),Q(1,4),Q(1,2),Q(3,4),Q(-1,10),Q(-1,4),Q(-1,2),Q(-3,4)):
        fine, eff = induced(t)
        assert all(fine(x,y,z)>0 for x in SIGNS for y in SIGNS for z in SIGNS)
        assert all(eff(x,y)==1+t*t*CHAR[x]*CHAR[y] for x in SIGNS for y in SIGNS)
        assert haar2(eff)==1
        eX=haar2(lambda x,y: eff(x,y)*CHAR[x])
        eY=haar2(lambda x,y: eff(x,y)*CHAR[y])
        eXY=haar2(lambda x,y: eff(x,y)*CHAR[x]*CHAR[y])
        assert (eX,eY,eXY)==(0,0,t*t)
        det=eff(True,True)*eff(False,False)-eff(True,False)*eff(False,True)
        assert det==4*t*t and det>0
        for _ in range(512):
            f={(x,y):Q(rng.randint(-12,12),rng.randint(1,11)) for x in SIGNS for y in SIGNS}
            fine_m=haar2(lambda x,y:sum((fine(x,y,z)*f[x,y] for z in SIGNS),Q(0))/2)
            eff_m=haar2(lambda x,y:eff(x,y)*f[x,y])
            assert fine_m==eff_m
            marked+=1
    print(f"PASS {marked}/{marked}: exact arbitrary signed marked-observable fine/effective transports")
    print("PASS 8/8: positive fine weight, normalized partition, two one-point cancellations")
    print("PASS 8/8: positive cross determinant and t^2 induced covariance")
    print("NEGATIVE: equal Z and first moments do not ensure third moment / factorized RG closure")
    print("BOUNDARY: finite Z2 characters; no original SU(N), Agda kernel, or UV theorem")

if __name__=="__main__":
    run()
