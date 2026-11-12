#!/usr/bin/env python3
"""Exact-rational bounded non-Cauchy example with O(1/k) increments.

Tests the E1 inference in the supplied proposed Yang--Mills gate proof:
|E_{k+1}-E_k| <= C/k is NOT a Cauchy theorem; regrouping indexes
without extra cancellation/summable control cannot create 2^-delta j.
No claim about the actual Wilson sequence is made.
"""
from fractions import Fraction

def sawtooth(k: int) -> Fraction:
    assert k >= 1
    stage = k.bit_length() - 1
    half = 1 << stage
    t = Fraction(k - half, half)
    return t if stage % 2 == 0 else 1 - t

def check(max_stage=17):
    for k in range(1, 1 << max_stage):
        step = abs(sawtooth(k+1) - sawtooth(k))
        assert step <= Fraction(2, k)
        assert Fraction(0) <= sawtooth(k) <= Fraction(1)
    for j in range(max_stage):
        assert sawtooth(1 << j) == (0 if j % 2 == 0 else 1)
        assert (1 << j) * Fraction(1, 1 << (j+1)) == Fraction(1,2)
        assert all(k <= (1 << (j+1)) for k in range(1 << j, 1 << (j+1)))
    print(f'PASS exact bounded rational sawtooth: {2**max_stage - 1} adjacent O(1/k) bounds')
    print(f'PASS {max_stage} alternating dyadic stage values 0/1 and harmonic-block lower bound 1/2')
    print('CONCLUSION: an O(1/k) one-step bound does NOT imply E1 Cauchy convergence.')

if __name__ == '__main__':
    check()
