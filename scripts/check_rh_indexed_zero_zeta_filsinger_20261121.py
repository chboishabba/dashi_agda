#!/usr/bin/env python3
"""Finite exact negative controls for k/time indexed zero/zeta/zeta² mode.
Source donors: Monster3BZeroZetaSquaredC3SeparationExact and Filsinger
phase polarity/time accounting. No analytic zeta, TLiftK or RH proof.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product

@dataclass(frozen=True)
class Frame:
    k: int
    mode: str
    sign: int
    residual: Fraction
    observed_zero: bool

def reflect(frame):
    return Frame(frame.k, {"zero":"zero","one":"one",
                           "zeta":"zeta2","zeta2":"zeta"}[frame.mode],
                 frame.sign,frame.residual,frame.observed_zero)

def phase_coeff(mode):
    # Exact Q(zeta3) basis, zeta3² = -1 - zeta3.
    return {"zero":(0,0),"one":(1,0),"zeta":(0,1),
            "zeta2":(-1,-1)}[mode]

def sum_phase(frames):
    return tuple(sum(phase_coeff(f.mode)[i] for f in frames) for i in (0,1))

def run():
    checks=0
    for k,sign,r in product(range(4),(-1,1),(-7,0,8)):
        for mode in ("zero","one","zeta","zeta2"):
            f=Frame(k,mode,sign,Fraction(r),True)
            assert reflect(reflect(f))==f
            assert reflect(f).k==f.k
            assert reflect(f).sign==f.sign
            assert reflect(f).residual==f.residual
            assert reflect(f).observed_zero==f.observed_zero
            checks+=1
    assert sum_phase((Frame(0,"one",1,Fraction(0),True),
                      Frame(0,"zeta",1,Fraction(0),True),
                      Frame(0,"zeta2",1,Fraction(0),True)))==(0,0)
    # Identical observed zero does not mean identical underlying modes.
    assert phase_coeff("zero")!=phase_coeff("zeta")
    assert phase_coeff("zero")!=phase_coeff("zeta2")
    assert phase_coeff("one")!=phase_coeff("zero")
    # Filsinger's source-indexed polarity lesson: identical observed zero
    # need not identify work/drive sign or an unmeasured physical state.
    a=Frame(3,"zeta",1,Fraction(9),True)
    b=Frame(3,"zeta",-1,Fraction(-9),True)
    assert a.observed_zero==b.observed_zero and a!=b
    assert reflect(a).residual == a.residual
    print(f"PASS: {checks} exact indexed reflection/sign/residual checks")
    print("PASS: Q(zeta3) balanced triple sums to 0, none is scalar zero")
    print("PASS: observed zero is non-injective; signed residual retained")
    print("NOT TESTED: source TLiftK, Galois Row0b, analytic zeta, kernel")
if __name__=="__main__":
    run()
