#!/usr/bin/env python3
"""Acceptance tests: three-sector equivariance, gauge invariance,
readout limitations and reproducibility. Self-contained stdlib."""
import unittest
import alexander_horned_c3_finite_SU2_gauge_simulator as S

class HornGaugeTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.G,cls.q,cls.section,cls.pair=S.build()
  cls.tower=S.tower(cls.q,cls.section,cls.pair,4)
 def test_recursive_child_commutators(self):
  for d in range(4):
   for address,expected in self.tower[d].items():
    self.assertEqual(S.comm(self.tower[d+1][address+(0,)],
                            self.tower[d+1][address+(1,)]),expected)
 def test_three_sector_C3_rotation(self):
  # Each sector carries its OWN source-group factor; R permutes
  # all three, and the bonding maps are factorwise identical.
  for d in range(4):
   p={(sector,address):value for sector in range(3)
      for address,value in self.tower[d].items()}
   children={(sector,address):value for sector in range(3)
      for address,value in self.tower[d+1].items()}
   for (sector,address),value in p.items():
    self.assertEqual(S.comm(children[sector,address+(0,)],
                            children[sector,address+(1,)]),value)
    self.assertEqual(p[((sector+1)%3,address)],value)
    self.assertEqual(children[((sector+1)%3,address+(0,))],
                     children[(sector,address+(0,))])
   self.assertEqual(len(children),3*2**(d+1))
 def test_conjugation_invariance_of_Wilson_trace(self):
  import random
  r=random.Random(41)
  for _ in range(60):
   a=r.choice(self.G);b=r.choice(self.G);u=r.choice(self.G)
   x=S.comm(a,b)
   a1=S.mul(S.mul(u,a),S.inv(u))
   b1=S.mul(S.mul(u,b),S.inv(u))
   observed=S.comm(a1,b1)
   self.assertEqual(observed,S.mul(S.mul(u,x),S.inv(u)))
   self.assertEqual(observed[0],x[0])
 def test_orientation_not_distinguishable_by_trace_alone(self):
  self.assertNotEqual(self.q,S.inv(self.q))
  self.assertEqual(self.q[0],S.inv(self.q)[0])
 def test_noise_free_exact_readout(self):
  sample=S.simulate(3,2,20,0.,4)
  self.assertTrue(all(row['ideal_halftrace']==-1.
                      and row['observed_halftrace']==-1.
                      for row in sample['rows']))
 def test_seeded_readout_is_deterministic(self):
  self.assertEqual(S.simulate(1,2,30,1.5,5),
                   S.simulate(1,2,30,1.5,5))

if __name__=='__main__':unittest.main(verbosity=2)
