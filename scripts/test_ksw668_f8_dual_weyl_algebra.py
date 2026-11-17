#!/usr/bin/env python3
"""Exact rational checks for the original F8 dual-electric-Weyl readouts.

Original KSW668 source/model attribution remains with its owners.
These identities do not assert covariant geometric curvature equivalence.
"""
from fractions import Fraction as Q
import itertools
import unittest


def E4(k, a, rr):
    return -k * (a + rr) / 4


def E5(k, a, eta, lap):
    return -k * (a + 2 * eta - lap) / 2


def residual(k, eta, rr, lap):
    return k * (lap + rr - 2 * eta) / 2


class ReadoutAlgebra(unittest.TestCase):
    def test_dual_cancellation_exact(self):
        values = [Q(-3, 7), Q(0), Q(5, 11)]
        for k, a, eta, rr, lap in itertools.product(values, repeat=5):
            self.assertEqual(E5(k, a, eta, lap) - 2 * E4(k, a, rr),
                             residual(k, eta, rr, lap))

    def test_double_readout_reconstruction(self):
        for n in range(-7, 8):
            k, a, eta, rr, lap = Q(1, 144), Q(n, 7), Q(n*n, 5), Q(-n, 3), Q(n + 1, 11)
            self.assertEqual(E5(k, a, eta, lap),
                             2 * E4(k, a, rr) + residual(k, eta, rr, lap))

    def test_etaeta_cancels(self):
        for n in range(11):
            k, eta, rr, lap = Q(n+1, n+2), Q(n, 4), Q(-n, 5), Q(n*n, 13)
            self.assertEqual(E5(k, Q(99), eta, lap) - 2*E4(k, Q(99), rr),
                             E5(k, Q(-99), eta, lap) - 2*E4(k, Q(-99), rr))


if __name__ == '__main__':
    unittest.main()
