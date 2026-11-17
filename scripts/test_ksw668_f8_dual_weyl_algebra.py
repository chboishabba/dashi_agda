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




class OriginalSourceFreeWeylSlice(unittest.TestCase):
    """Exact t=4/3, same original moving normal and TT wave constraints."""
    def test_original_geometry_and_source_free_normal(self):
        self.assertEqual(Q(16,9)*(-Q(15,16)**2+Q(-9,16)**2),-1)
        self.assertEqual(Q(16,9)*(-Q(-9,16)**2+Q(15,16)**2),1)

    def test_bulk_and_differentiated_wall_constraints(self):
        for A,B,E in itertools.product([Q(-2),Q(0),Q(3,7)],repeat=3):
            C=A-B+4*E
            D=Q(15,17)*A-Q(15,34)*B+Q(118,85)*E
            self.assertEqual(-A+B+C-4*E,0)
            self.assertEqual(-675*(A+C)+1530*D+576*E,0)

    def test_same_original_linearized_electric_weyl_equals_SMS(self):
        for A,B,E in itertools.product([Q(-2),Q(0),Q(3,7)],repeat=3):
            C=A-B+4*E
            D=Q(15,17)*A-Q(15,34)*B+Q(118,85)*E
            Egeom=-Q(129,512)*A+Q(3,32)*B-Q(177,512)*C+Q(135,256)*D
            Hddot=Q(9,34)*A+Q(81,544)*B-Q(129,136)*E
            Esms=-Hddot/2-Q(9,8)*E+Q(9,32)*B
            self.assertEqual(Egeom,Esms)
            self.assertEqual(Esms,-Q(9,68)*A+Q(225,1088)*B-Q(177,272)*E)

if __name__ == '__main__':
    unittest.main()
