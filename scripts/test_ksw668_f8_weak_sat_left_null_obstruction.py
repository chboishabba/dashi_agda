import unittest
import sympy as sp
from ksw668_f8_weak_sat_left_null_obstruction import sbp2,left_null,audit
class OriginalGlobalPhysicalBoundaryCompatibility(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.j=audit()
 def test_all_left_nulls(self):
  for n in range(3,14):self.assertEqual(sbp2(n).T*left_null(n),sp.zeros(n,1))
 def test_rank_co_dimension_one(self):
  for n in range(3,14):self.assertEqual(sbp2(n).rank(),n-1)
 def test_end_parity(self):
  for n in range(3,14):self.assertEqual(left_null(n)[0],(-1)**(n-1))
 def test_generic_wall_far_unrepairable(self):self.assertTrue(all(x['bad_left_null']!=0 for x in self.j['rows']))
 def test_compatible_pair_has_solution(self):
  for n in range(3,14):
   D=sbp2(n);l=left_null(n);g=sp.zeros(n,1);g[0]=1;g[-1]=-l[0]
   self.assertEqual(D.row_join(g).rank(),D.rank())
 def test_does_not_rule_out_joint_SAT(self):self.assertFalse(self.j['joint_P_M_U_or_nonlocal_boundary_repair_disproved'])
 def test_reject_two_nodes(self):
  with self.assertRaises(ValueError):sbp2(2)
if __name__=='__main__':unittest.main()
