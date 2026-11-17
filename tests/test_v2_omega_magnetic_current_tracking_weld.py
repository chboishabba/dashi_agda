import unittest, math
import numpy as np
from dataclasses import replace
from scipy.integrate import solve_ivp
from v2_omega_coupled_magnetic_torque import Model
from v2_omega_nonlinear_memory_torque import Memory,match_output,periodic_state
from v2_omega_magnetic_current_tracking_weld import Tracking,reference,maps,controlled_step,global_certificate,experiment

class CurrentTrackingWeld(unittest.TestCase):
    def test_positive_incremental_inductance(self):
        for aware in (True,False):
            q=match_output(Model(),Memory(),20.,aware)
            c=global_certificate(control=q)
            self.assertGreater(c['min_incremental_inductance_bound_h'],.03)
    def test_voltage_tube_certified_both_controls(self):
        for aware in (True,False):
            q=match_output(Model(),Memory(),20.,aware)
            c=global_certificate(control=q)
            self.assertTrue(c['voltage_certified'])
            self.assertTrue(c['current_certified'])
            self.assertTrue(c['memory_tube_invariant_sufficient'])
            self.assertLess(c['sufficient_voltage_bound_v'],310)
    def test_tracking_exact_algebra_in_tube(self):
        m=Model();mem=Memory();control=match_output(m,mem,20,True)
        u=np.array(control['u']);v=np.array(control['v']);gain=Tracking()
        for theta in np.linspace(0,2*math.pi/m.poles,40):
            r,_=reference(theta,m,u,v)
            for sign in (-1,1):
                i=r+sign*.02*np.array([1.,-.75])
                z=r+sign*.01*np.array([-.3,1.])
                f=controlled_step(theta,m.omega+.05,i,z,u,v,gain,m,mem)
                self.assertTrue(np.allclose(f['error_derivative'],-gain.gain_hz*f['error'],atol=1e-11,rtol=0))
                self.assertTrue(f['voltage_ok'])
    def test_reference_is_invariant(self):
        m=Model();mem=Memory();q=match_output(m,mem,20,True)
        u=np.array(q['u']);v=np.array(q['v']);_,U,V=periodic_state(m,mem,u,v)
        for theta in np.linspace(0,2*math.pi/m.poles,30):
            r,_=reference(theta,m,u,v)
            z=m.arrays()[4]+math.sin(m.poles*theta)*U+math.cos(m.poles*theta)*V
            f=controlled_step(theta,m.omega,r,z,u,v)
            self.assertLess(np.linalg.norm(f['error_derivative']),1e-11)
    def test_tracking_convergence_prescribed_speed(self):
        m=Model();mem=Memory();q=match_output(m,mem,20,True)
        u=np.array(q['u']);v=np.array(q['v']);c,U,V=periodic_state(m,mem,u,v)
        eps=.02;gain=Tracking();z0=c+V
        r0,_=reference(0,m,u,v)
        voltage=[]
        def rhs(t,y):
            theta=m.omega*t;i=y[:2];z=y[2:]
            f=controlled_step(theta,m.omega,i,z,u,v,gain,m,mem)
            voltage.append(float(np.max(abs(f['v']))))
            return [*f['actual_di'],*((i-z)/mem.check()[1])]
        sol=solve_ivp(rhs,(0,.008),[* (r0+np.array([eps,-eps])),*z0],rtol=1e-10,atol=1e-11,max_step=2e-5)
        self.assertTrue(sol.success)
        end=sol.y[:2,-1]-reference(m.omega*.008,m,u,v)[0]
        self.assertLess(np.max(abs(end)),1e-6)
        self.assertLess(max(voltage),m.voltage_limit)
    def test_wrong_lag_tube_rejected(self):
        c=global_certificate(tracking=Tracking(initial_error_bound_a=.025,memory_error_bound_a=.025))
        self.assertFalse(c['memory_tube_invariant_sufficient'])
        self.assertGreater(c['memory_tube_required_a'],.025)
    def test_insufficient_bus_negative_control(self):
        c=global_certificate(m=replace(Model(),voltage_limit=280.))
        self.assertFalse(c['voltage_certified'])
    def test_large_tracking_error_negative_control(self):
        c=global_certificate(tracking=Tracking(initial_error_bound_a=.5,memory_error_bound_a=.5))
        self.assertFalse(c['voltage_certified'])
    def test_invalid_gain(self):
        with self.assertRaises(ValueError):global_certificate(tracking=Tracking(gain_hz=0))
    def test_speed_budget_degrades_headroom(self):
        a=global_certificate(tracking=Tracking(speed_deviation_rpm=1.))
        b=global_certificate(tracking=Tracking(speed_deviation_rpm=120.))
        self.assertGreater(b['sufficient_voltage_bound_v'],a['sufficient_voltage_bound_v'])
    def test_schema_open_gate(self):
        q=experiment()
        self.assertEqual(len(q['modelled_targets']),2)
        self.assertIn('real switched PWM tracking',q['open_gates'])

if __name__=='__main__':unittest.main()

class CoupledCurrentRotorNumerical(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from v2_omega_magnetic_current_tracking_weld import execute_coupled
        cls.aware=execute_coupled(aware=True)
        cls.naive=execute_coupled(aware=False)
    def test_nonlinear_energy_cancellation(self):
        for q in (self.aware,self.naive):
            self.assertLess(abs(q['balance_residual_j']),.0001)
    def test_voltage_not_clipped(self):
        for q in (self.aware,self.naive):
            self.assertEqual(q['voltage_clipped_fraction'],0.)
            self.assertLess(q['peak_command_voltage_v'],320.)
    def test_torque_not_saturated(self):
        for q in (self.aware,self.naive):
            self.assertEqual(q['torque_saturated_fraction'],0.)
    def test_actual_tracking_small(self):
        for q in (self.aware,self.naive):
            self.assertLess(q['peak_current_error_a'],1e-5)
    def test_recovery_fixed_while_motor_saving(self):
        self.assertLess(abs(self.aware['last_cycle_export_bus_w']-self.naive['last_cycle_export_bus_w']),.05)
        self.assertGreater(self.naive['last_cycle_drive_w']-self.aware['last_cycle_drive_w'],1.5)
