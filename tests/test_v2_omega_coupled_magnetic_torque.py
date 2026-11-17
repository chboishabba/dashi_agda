import sys,unittest,math
from pathlib import Path
from dataclasses import replace
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from v2_omega_coupled_magnetic_torque import Model,coefficient,optimum,evaluate,matched_output,variants

class CoupledMaxcut(unittest.TestCase):
 def setUp(self):self.m=Model()
 def test_spd(self):self.m.arrays()
 def test_bad_incremental_inductance(self):
  with self.assertRaises(ValueError):replace(self.m,mean_L=((.001,0),(0,.001))).arrays()
 def test_full_cycle_energy_balances(self):
  q=optimum(self.m,.25);self.assertAlmostEqual(q['energy_balance_residual_w'],0,places=9)
 def test_torque_analytic_matches_samples(self):
  for u,v in [([.2,-.4],[.1,.3]),([-.3,.5],[.4,-.2]),([0,0],[.2,-.3])]:
   q=evaluate(self.m,u,v);self.assertAlmostEqual(q['shaft_w'],q['shaft_from_sampled_torque_w'],places=9)
 def test_global_ac_copper_cauchy_optimum(self):
  q=optimum(self.m,.5);self.assertLess(abs(q['optimality_slack_w']),1e-9)
 def test_perturbations_never_beat_budget_optimum(self):
  rng=np.random.default_rng(5);B=.4;best=optimum(self.m,B)
  for _ in range(250):
   z=rng.normal(size=4);z*=math.sqrt(2*B/(z[0]**2*self.m.R[0]+z[1]**2*self.m.R[1]+z[2]**2*self.m.R[0]+z[3]**2*self.m.R[1]));q=evaluate(self.m,z[:2],z[2:],n=256);self.assertLessEqual(q['shaft_w'],best['shaft_w']+1e-9)
 def test_no_angular_coupling_no_torque(self):
  m=replace(self.m,cos_L=((0.,0.),(0.,0.)),sin_L=((0.,0.),(0.,0.)))
  q=evaluate(m,[.5,.5],[.3,-.3]);self.assertAlmostEqual(q['shaft_w'],0)
 def test_reverse_phase_reverses_electromechanical_power(self):
  q=evaluate(self.m,[.5,.3],[.2,-.2]);p=evaluate(self.m,[-.5,-.3],[-.2,.2]);self.assertAlmostEqual(q['shaft_w'],-p['shaft_w'])
 def test_fixed_output_different_loss_and_torque(self):
  x=variants();coupled=x['coupled']['matched_output'];no=x['uncoupled']['matched_output'];op=x['opposing_mutual']['matched_output']
  self.assertLess(coupled['shaft_w'],no['shaft_w']);self.assertLess(no['shaft_w'],op['shaft_w'])
  for q in (coupled,no,op):self.assertAlmostEqual(q['exported_bus_w'],20,places=7)
 def test_copper_only_pays_shaft_difference(self):
  x=variants();a=x['coupled']['matched_output'];b=x['uncoupled']['matched_output'];self.assertAlmostEqual(b['shaft_w']-a['shaft_w'],b['copper_total_w']-a['copper_total_w'],places=8)
 def test_common_converter_is_not_tuned(self):
  x=variants();self.assertEqual(len({r['model']['bus_eta'] for r in x.values()}),1)
 def test_voltage_certificate_and_current(self):
  for row in variants().values():
   q=row['matched_output'];self.assertTrue(q['current_certified']);self.assertTrue(q['grid_voltage_certified']);self.assertLessEqual(q['sampled_peak_voltage_v'],q['grid_lipschitz_voltage_bound_v'])
 def test_sufficient_global_voltage_bound(self):
  q=matched_output(self.m);self.assertTrue(q['continuous_voltage_certified']);self.assertLess(q['continuous_voltage_sufficient_bound_v'],320)
 def test_wrong_voltage_cap_fails(self):
  m=replace(self.m,voltage_limit=80);self.assertFalse(matched_output(m)['grid_voltage_certified'])
 def test_higher_beta_doesnt_create_shaft_work(self):
  a=evaluate(self.m,[.3,.2],[.2,-.2]);b=evaluate(replace(self.m,beta=.00005),[.3,.2],[.2,-.2]);self.assertAlmostEqual(a['shaft_w'],b['shaft_w'])
 def test_export_and_storage_not_double_counted(self):
  q=matched_output(self.m);self.assertAlmostEqual(q['shaft_w'],q['copper_total_w']+q['raw_bus_w']);self.assertGreater(q['raw_bus_w'],q['exported_bus_w'])

if __name__=='__main__':unittest.main()

class WithinGeometryControls(unittest.TestCase):
 def test_coordinated_control_marginal_gain(self):
  from v2_omega_coupled_magnetic_torque import same_geometry_control_comparison
  q=same_geometry_control_comparison()
  self.assertGreater(q['shaft_saving_w'],0)
  self.assertLess(q['shaft_saving_w'],.1)
  self.assertAlmostEqual(q['shaft_saving_w'],q['copper_saving_w'],places=9)
 def test_same_geometry_output_and_voltage(self):
  from v2_omega_coupled_magnetic_torque import same_geometry_control_comparison
  q=same_geometry_control_comparison()
  for r in (q['optimal_joint'],q['uncoupled_designed_timing']):
   self.assertAlmostEqual(r['exported_bus_w'],20)
   self.assertTrue(r['continuous_voltage_certified'])
   self.assertTrue(r['current_certified'])
 def test_zero_direction_rejected(self):
  from v2_omega_coupled_magnetic_torque import matched_control_direction
  with self.assertRaises(ValueError): matched_control_direction(Model(),[0,0],[0,0])
