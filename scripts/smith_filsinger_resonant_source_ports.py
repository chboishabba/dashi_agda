#!/usr/bin/env python3
"""Analytic resonant-source test, not a Smith/Filsinger hardware netlist.
Runnable locally, Python standard library; exposes useful vs reactive power.
"""
from dataclasses import dataclass
from math import pi, sqrt
import unittest
@dataclass(frozen=True)
class ResonantPort:
    c: float=100e-9
    f: float=7800.0
    r_load: float=2500.
    r_shunt: float=1e6
    r_internal: float=20000.
    @property
    def l(self): return 1/((2*pi*self.f)**2*self.c)
    @property
    def conductance(self): return 1/self.r_load+1/self.r_shunt+1/self.r_internal
    def admittance(self,frequency):
        w=2*pi*frequency
        return complex(self.conductance,w*self.c-1/(w*self.l))
    def powers_at_resonance(self,drive_watts):
        # Optimistic single-frequency resonant steady state, real drive
        vpeak=sqrt(2*drive_watts/self.conductance)
        return dict(source=drive_watts,voltage_peak=vpeak,
          load=vpeak*vpeak/(2*self.r_load),
          shunt=vpeak*vpeak/(2*self.r_shunt),
          internal=vpeak*vpeak/(2*self.r_internal),
          reactive_var=pi*self.f*self.c*vpeak*vpeak)

def source_gap(pdrive,pout,loss=0,storage_rate=0):
    # net external port power necessary for claimed delivered REAL power
    return pout+loss+storage_rate-pdrive

class Tests(unittest.TestCase):
    def test_resonant_l(self):self.assertAlmostEqual(ResonantPort().l,.004163427993)
    def test_zero_resonance_susceptance(self):self.assertAlmostEqual(ResonantPort().admittance(7800).imag,0,places=12)
    def test_real_energy_conserved(self):
        p=ResonantPort().powers_at_resonance(12)
        self.assertAlmostEqual(p['source'],p['load']+p['shunt']+p['internal'])
    def test_reactive_larger_than_drive(self):
        self.assertGreater(ResonantPort().powers_at_resonance(12)['reactive_var'],12*10)
    def test_reactive_not_added_to_real(self):
        p=ResonantPort().powers_at_resonance(12)
        self.assertLess(p['load'],p['source'])
    def test_more_shunt_increases_conductance(self):
        self.assertGreater(ResonantPort(r_shunt=1e6).conductance,ResonantPort(r_shunt=4e6).conductance)
    def test_smith_claim_gap(self):self.assertEqual(source_gap(12,8000*20),159988)
    def test_one_minute_gap(self):self.assertEqual(source_gap(12,160000)*60,9599280)
    def test_four_hundred_ohm_load(self):self.assertEqual(8000/20,400)
    def test_total_env_not_source_identity(self):
        assert sum((159988,0,0))==sum((0,159988,0))
    def test_storage_alternative(self):
        self.assertEqual(source_gap(12,160000,storage_rate=-159988),0)
if __name__=='__main__':unittest.main(verbosity=2)
