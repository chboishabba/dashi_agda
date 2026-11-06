"""Conservation referee fixtures: source geometry independent from collision solver."""
import math
import unittest
from kozyrev_optical_event_ledger import C, RayLedger, specular

class OpticalLedger(unittest.TestCase):
    def test_reflection_ledger(self):
        r=RayLedger.emit((0.,0.),(1.,0.),9000.)
        out=specular((1.,0.),(-1.,0.))
        r.hit((1.,0.),out,1)
        z=r.close('escape',(-1.,0.))
        self.assertAlmostEqual(z['wall_force_N'][0],18000/C)
        self.assertAlmostEqual(z['momentum_residual_N'],0,places=16)
        self.assertAlmostEqual(z['angular_residual_Nm'],0,places=16)
    def test_absorbing_wall(self):
        r=RayLedger.emit((0.,0.),(1.,0.),9000.)
        r.hit((1.,0.),(-1.,0.),.95)
        z=r.close('escape',(-2.,0.))
        self.assertAlmostEqual(z['wall_absorption_W'],450)
        self.assertAlmostEqual(z['energy_residual_W'],0,places=8)
        self.assertAlmostEqual(z['momentum_residual_N'],0,places=16)
    def test_signed_torque_and_target(self):
        r=RayLedger.emit((-2.,1.),(1.,0.),9000.)
        # first ray travels at y=1, reflects upward at x=0
        r.hit((0.,1.),(0.,1.),1)
        z=r.close('target',(0.,2.))
        self.assertLess(z['wall_torque_Nm'],0)
        self.assertLess(abs(z['angular_residual_Nm']),1e-15)
    def test_unresolved_not_escape(self):
        r=RayLedger.emit((0.,0.),(1.,0.),200.)
        z=r.close('unresolved',(1.,0.))
        self.assertEqual(z['kind'],'unresolved')
        self.assertEqual(z['terminal_power_W'],200)
    def test_uniform_scaling(self):
        values=[]
        for k in (0.1,1.,10.):
            r=RayLedger.emit((-2*k,k),(1.,0.),9000.)
            r.hit((0.,k),(0.,1.),1.)
            z=r.close('escape',(0.,2*k))
            values.append(z['wall_torque_Nm']/k)
            self.assertLess(abs(z['angular_residual_Nm']),1e-15)
        self.assertAlmostEqual(max(values),min(values),places=14)
    def test_reject_disconnected_event(self):
        r=RayLedger.emit((0.,0.),(1.,0.),200.)
        with self.assertRaises(ValueError):
            r.hit((0.,1.),(-1.,0.),1.)
        with self.assertRaises(ValueError):
            r.close('escape',(0.,1.))
    def test_reject_invalid_reflection(self):
        with self.assertRaises(ValueError):specular((1.,0.),(2.,0.))
if __name__=='__main__':unittest.main()
