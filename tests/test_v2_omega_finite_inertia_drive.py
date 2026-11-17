import math
import unittest
from dataclasses import replace
from v2_omega_finite_inertia_drive import Drive,fields,comparison,execute
from v2_omega_coupled_magnetic_torque import Model
from v2_omega_nonlinear_memory_torque import Memory,match_output,periodic_state
import numpy as np

class RotorDriveWeld(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result=comparison()
    def test_balanced_machine_cycles(self):
        for n in ('memory_aware','copper_only'):
            z=self.result[n]
            self.assertLess(abs(z['cycle']['balance_residual_j']),1e-5)
            self.assertLess(abs(z['cycle']['magnetic_storage_rate_w']),.002)
            self.assertTrue(z['numerically_steady_last_cycle'])
            self.assertLess(z['cycle']['saturation_fraction'],.001)
    def test_near_equal_export(self):
        a=self.result['memory_aware']['cycle']['export_bus_signed_ideal_w']
        b=self.result['copper_only']['cycle']['export_bus_signed_ideal_w']
        self.assertAlmostEqual(a,20.,delta=.02)
        self.assertAlmostEqual(a,b,delta=.02)
    def test_motor_shaft_saving(self):
        self.assertGreater(self.result['actual_dynamic_drive_delta_w'],2.0)
        self.assertLess(self.result['actual_dynamic_drive_delta_w'],2.5)
    def test_voltage_and_current(self):
        for n in ('memory_aware','copper_only'):
            z=self.result[n]
            self.assertTrue(z['sampled_voltage_feasible'])
            self.assertTrue(z['sampled_current_feasible'])
            self.assertLess(z['peak_motor_torque_nm'],z['parameters']['torque_max_nm'])
    def test_finite_ripple(self):
        for n in ('memory_aware','copper_only'):
            self.assertLess(self.result[n]['last_cycle_speed_variation_rpm'],1)
    def test_analytical_periodic_limit(self):
        for n,aware in (('memory_aware',True),('copper_only',False)):
            static=match_output(Model(),Memory(),20.,aware)
            sim=self.result[n]['cycle']
            self.assertAlmostEqual(sim['export_bus_signed_ideal_w'],static['bus_w'],delta=.02)
    def test_storage_does_not_fake_power(self):
        for n in ('memory_aware','copper_only'):
            c=self.result[n]['cycle']
            lhs=c['drive_w'];rhs=sum(c[k] for k in ('export_raw_w','copper_w','memory_w','friction_w','rotor_storage_rate_w','magnetic_storage_rate_w'))
            self.assertAlmostEqual(lhs,rhs,delta=.001)
    def test_torque_limit_negative_control(self):
        z=execute(drive=Drive(torque_max_nm=.08))
        self.assertGreater(z['cycle']['saturation_fraction'],.99)
        self.assertLess(z['cycle']['rotor_storage_rate_w'],-5.)
        self.assertFalse(z['numerically_steady_last_cycle'])
    def test_light_rotor_negative_control(self):
        z=execute(drive=Drive(inertia_kgm2=.0002))
        self.assertGreater(z['last_cycle_speed_variation_rpm'],10.)
        self.assertLess(abs(z['cycle']['balance_residual_j']),.0001)
    def test_invalid_drive(self):
        for d in (Drive(inertia_kgm2=0),Drive(torque_max_nm=0),Drive(turns=2),Drive(max_step_s=0)):
            with self.assertRaises(ValueError): execute(drive=d)
    def test_torque_on_rotor_sign(self):
        m=Model();mem=Memory();q=match_output(m,mem,20.,True)
        u=np.array(q['u']);v=np.array(q['v']);c,U,V=periodic_state(m,mem,u,v)
        f=fields(0,m.omega,c+V,m,mem,u,v)
        eps=1e-6
        plus=fields(eps,m.omega,c+V,m,mem,u,v)
        minus=fields(-eps,m.omega,c+V,m,mem,u,v)
        # A fixed-current/fixed-memory coenergy torque depends only on L(theta).
        # Reversible fixed-current coenergy gradient = -physical reaction convention.
        E=lambda th: .5*f['i']@(m.arrays()[0]+np.cos(m.poles*th)*m.arrays()[1]+np.sin(m.poles*th)*m.arrays()[2])@f['i']
        self.assertAlmostEqual((E(eps)-E(-eps))/(2*eps),f['torque'],delta=1e-6)

if __name__=='__main__':unittest.main()
