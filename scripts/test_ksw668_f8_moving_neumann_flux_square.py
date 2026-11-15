#!/usr/bin/env python3
import unittest,math
from ksw668_f8_moving_neumann_flux_square import symbolic,evaluate,audit
class OriginalMovingFluxSquare(unittest.TestCase):
    def test_exact_sympy_identity(self):self.assertTrue(symbolic()['exact_forced_boundary_square'])
    def test_exact_t43_rational_identity(self):self.assertIn('10G²/3',symbolic()['original_t43_identity'])
    def test_t1_wall(self):
        d=evaluate(1,1,.1);self.assertLessEqual(d['actual_incoming_minus_outgoing_characteristic_flux'],d['uniform_forced_bound'])
    def test_t43_wall(self):
        d=evaluate(4/3,1,.1);self.assertLessEqual(d['actual_incoming_minus_outgoing_characteristic_flux'],d['uniform_forced_bound'])
    def test_t2_wall(self):
        d=evaluate(2,1,.1);self.assertLessEqual(d['actual_incoming_minus_outgoing_characteristic_flux'],d['uniform_forced_bound'])
    def test_vector_TT(self):self.assertTrue(audit()['original_forced_wall_flux_bound_closed'])
    def test_homogeneous_absorption(self):self.assertTrue(evaluate(1.7,[.4,-.2],[0,0])['homogeneous_dissipative'])
    def test_vertex_attains_bound(self):
        d=evaluate(4/3,.2/(-3/5),.2)
        self.assertAlmostEqual(d['actual_incoming_minus_outgoing_characteristic_flux'],d['uniform_forced_bound'],places=12)
    def test_uniform_2sqrt5(self):self.assertAlmostEqual(evaluate(2,0,1)['bound_constant'],2*math.sqrt(5))
    def test_zero_source_flux(self):self.assertLess(evaluate(1.5,1,0)['actual_incoming_minus_outgoing_characteristic_flux'],0)
    def test_outside_original_rejected(self):
        with self.assertRaises(ValueError):evaluate(3,0,0)
    def test_no_receiver_promotion(self):self.assertTrue(audit()['full_time_discrete_CFL_and_receiver_trace_open'])
if __name__=='__main__':unittest.main(verbosity=2)
