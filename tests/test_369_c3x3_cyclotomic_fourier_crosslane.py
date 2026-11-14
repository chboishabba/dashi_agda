"""Finite exact C3xC3 character algebra regression, physically non-promoting."""
import importlib.util
from pathlib import Path
import unittest

P=Path(__file__).resolve().parents[1]/"scripts"/"check_369_c3x3_cyclotomic_fourier_crosslane.py"
s=importlib.util.spec_from_file_location("c3crosslane",P)
m=importlib.util.module_from_spec(s)
s.loader.exec_module(m)

class Cyclotomic369CrossLaneTests(unittest.TestCase):
    def test_exact_character_contract(self):
        receipt=m.exact_receipt()
        self.assertTrue(receipt["character_homomorphism_729_checks"])
        self.assertTrue(receipt["convolution_9_frequency_checks"])
        self.assertTrue(receipt["parseval_exact"])
        self.assertFalse(receipt["NS_physical_nonlinearity_estimated"])
        self.assertFalse(receipt["YM_Wilson_Rg_estimated"])
        self.assertFalse(receipt["source_carrier_identifications_kernel_proved"])
    def test_1_plus_omega_plus_omega_squared_is_zero(self):
        self.assertEqual(m.plus(m.plus(m.ONE,m.OMEGA),m.OMEGA2),m.ZERO)
    def test_all_phase_character_orbits(self):
        for k in m.GROUP:
            self.assertEqual(m.character(k,(0,0)),m.ONE)
            self.assertEqual(m.character(k,m.add_g((1,0),(2,0))),m.ONE)
            self.assertEqual(m.character(k,m.add_g((0,1),(0,2))),m.ONE)
    def test_convolution_identity_and_zero_output_witness(self):
        delta={x:(1,0) if x==(0,0) else (0,0) for x in m.GROUP}
        const={x:(1,0) for x in m.GROUP}
        self.assertEqual(m.convolution(delta,const),const)
        self.assertEqual(m.add_g((1,2),(2,1)),(0,0))
if __name__=="__main__":unittest.main()
