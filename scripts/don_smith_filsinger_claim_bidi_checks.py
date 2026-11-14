#!/usr/bin/env python3
"""Conditional source/claim BIDI sanity checks. No device power receipt."""
from dataclasses import dataclass
from math import pi
import unittest
@dataclass(frozen=True)
class Claim:
    owner: str
    prediction: str
    required: tuple
claims=(
 Claim("Smith MXNL02000035A", "resonant voltage and load power", ("original circuit", "all source and load work")),
 Claim("Filsinger ZVS", "switching frequency and waveform", ("actual topology", "Vds and current traces")),
 Claim("Filsinger shunts", "resistor dissipation and frequency pulling", ("R endpoints", "synchronised V and frequency")),
 Claim("Filsinger earth", "signed Earth-port work", ("electrode chemistry", "ground voltage and current", "drive input")),
 Claim("Filsinger portable", "mode phase and extracted antenna power", ("Maxwell boundary solve", "antenna feed", "incident spectrum")),
 Claim("Filsinger cosmic", "calibrated received/deposited radiation work", ("radiation type", "flux", "transduction losses")),
 Claim("Model-derived two-mode", "current Lissajous", ("coherent source", "complex modal transfer functions"))
)
def energy(c,v):return .5*c*v*v
def all_ports_measured(p):return all(p.get(k,False) for k in ("drive","earth","em","particle","load","loss","storage"))
class Checks(unittest.TestCase):
 def test_seven(self):self.assertEqual(len(claims),7)
 def test_forward_and_reverse(self):self.assertTrue(all(c.prediction and c.required for c in claims))
 def test_different_owners(self):self.assertNotEqual(claims[0].owner,claims[1].owner)
 def test_earth_distinct_from_portable(self):self.assertNotEqual(claims[3].required,claims[4].required)
 def test_shunt_watts(self):self.assertEqual(1500**2/1e6,2.25)
 def test_Q(self):self.assertGreater(2*pi*7800*3.33e-6*1e6,160000)
 def test_cap_energy(self):self.assertAlmostEqual(energy(3.33e-6,1500),3.74625)
 def test_sens(self):self.assertAlmostEqual(5/7800,.000641025641025641)
 def test_partial_ports(self):self.assertFalse(all_ports_measured({"earth":True}))
 def test_complete_ports(self):self.assertTrue(all_ports_measured(dict.fromkeys(("drive","earth","em","particle","load","loss","storage"),True)))
 def test_ambiguity_world0(self):self.assertAlmostEqual(6.7+0-2-4.7,0)
 def test_ambiguity_world1(self):self.assertAlmostEqual(6.7+1-2-5.7,0)
if __name__=="__main__": unittest.main(verbosity=2)
