import unittest
from ksw668_f8_ternary_channel_drift import inspect, OPERATOR

def row():
    return dict(intrinsic_4D_weyl_spatial_operator=OPERATOR,raw_mode_values=[1.,2.,3.],retarded_TT_yy_scaled_by_eps4=6.,far_mode_values=[0.]*3,receiver_mode_intrinsic_4D_electric_Weyl=[1.,-2.,4.],receiver_intrinsic_4D_electric_Weyl=3.,far_mode_intrinsic_4D_electric_Weyl=[0.]*3,receiver_mode_projected_5D_electric_Weyl=[2.,-3.,4.],receiver_projected_5D_electric_Weyl=3.,far_mode_projected_5D_electric_Weyl=[0.]*3)
class Guard(unittest.TestCase):
    def test_valid(self): self.assertFalse(inspect([row(),row()])['both_Weyl_convergence_certified'])
    def test_missing(self):
        a=row(); del a['intrinsic_4D_weyl_spatial_operator']; self.assertRaises(ValueError,inspect,[a,row()])
    def test_mixed(self):
        a=row(); a['intrinsic_4D_weyl_spatial_operator']='legacy_axial'; self.assertRaises(ValueError,inspect,[a,row()])
    def test_both_legacy(self):
        a=row(); a['intrinsic_4D_weyl_spatial_operator']='legacy_axial'; self.assertRaises(ValueError,inspect,[a,a])
    def test_nonfinite(self):
        a=row(); a['far_mode_values'][0]=float('nan'); self.assertRaises(ValueError,inspect,[a,row()])
    def test_bad_sum(self):
        a=row(); a['receiver_intrinsic_4D_electric_Weyl']=0.; self.assertRaises(ValueError,inspect,[a,row()])
    def test_bad_length(self):
        a=row(); a['raw_mode_values']=[6.]; self.assertRaises(ValueError,inspect,[a,row()])
    def test_count(self): self.assertRaises(ValueError,inspect,[row()])
if __name__=='__main__': unittest.main(verbosity=2)
