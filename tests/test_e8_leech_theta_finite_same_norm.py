"""CPU exact-integer regression for original E8 coset-shell certificate.

These assert finite exact coefficients, not full modularity or theta equality.
"""
import importlib.util
from pathlib import Path
import unittest

path=Path(__file__).resolve().parent.parent/"scripts"/"check_e8_leech_theta_finite_same_norm.py"
spec=importlib.util.spec_from_file_location("e8theta",path)
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

class E8LeechFiniteCoefficients(unittest.TestCase):
    def test_norm_two_to_ten_shells(self):
        self.assertEqual(mod.integer_e8_shell_counts(5),
            [1,240,2160,6720,17520,30240])
    def test_modular_leech_candidate_first_coefficients(self):
        self.assertEqual(mod.leech_modular_prediction(4),
            [1,0,196560,16773120,398034000])
    def test_finite_dirichlet_convolution(self):
        for n in range(1,12):
            self.assertEqual(mod.sigma_power(n,3),
                sum(d**3 for d in range(1,n+1) if n%d==0))
    def test_first_shell_arithmetic_does_not_prove_infinite(self):
        report=mod.check(5)
        self.assertFalse(report["theta_e8_equals_e4_all_coefficients_proved"])
        self.assertFalse(report["theta_leech_equals_modular_candidate_all_coefficients_proved"])
        self.assertFalse(report["mellin_absolute_convergence_proved"])
        self.assertFalse(report["leech_rootless_actual_lattice_enumerated"])
        self.assertTrue(report["e8_e4_equal_through_bound"])
    def test_invalid_bounds_fail_closed(self):
        for n in (-1,1.2):
            with self.assertRaises(ValueError):
                mod.integer_e8_shell_counts(n)

if __name__=="__main__":unittest.main()
