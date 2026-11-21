#!/usr/bin/env python3
"""Finite exact k-indexed phase/signed-residual commuting-square checks.
Not an Agda kernel check, a proof of RH, or a physical Filsinger model.
"""
from dataclasses import dataclass
from itertools import product

@dataclass(frozen=True)
class Frame:
    k: int
    mode: str
    sign: int
    residual: int
    observed_zero: bool

INVERSE = {'zero': 'zero', 'one': 'one',
           'zeta': 'zeta2', 'zeta2': 'zeta'}

def reflect(f):
    return Frame(f.k, INVERSE[f.mode], f.sign, f.residual, f.observed_zero)

def advance(f):
    return Frame(f.k + 1, f.mode, f.sign, f.residual, f.observed_zero)

def lossy(f):
    return Frame(f.k + 1, 'zero', f.sign, 0, f.observed_zero)

def run():
    checked = 0
    for k, mode, sign, residual, zero in product(
            range(10), INVERSE, (-1, 1), (-9, 0, 7), (False, True)):
        f = Frame(k, mode, sign, residual, zero)
        assert advance(reflect(f)) == reflect(advance(f))
        assert advance(advance(reflect(f))) == reflect(advance(advance(f)))
        assert reflect(reflect(f)) == f
        assert advance(f).k == k + 1
        assert (advance(f).sign, advance(f).residual,
                advance(f).observed_zero) == (sign, residual, zero)
        assert f.mode != 'zero' or advance(f).mode == 'zero'
        checked += 1
    assert lossy(Frame(1, 'zeta', -1, 7, True)).residual != 7
    assert lossy(Frame(1, 'zeta', -1, 7, True)).mode != 'zeta'
    # Canonical Q(zeta_3) coordinate sum: 1 + zeta + zeta² = 0.
    assert tuple(sum(t[i] for t in ((1, 0), (0, 1), (-1, -1)))
                 for i in (0, 1)) == (0, 0)
    print(f"PASS {checked} finite indexed transition/reflection checks")
    print("PASS lossy mode/residual update rejected as information-preserving")
    print("NOT CHECKED: Agda, RH, source Hecke/automorphic theta lift")

if __name__ == '__main__':
    run()
