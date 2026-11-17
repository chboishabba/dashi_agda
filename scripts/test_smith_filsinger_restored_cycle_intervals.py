"""Synthetic exact-rational countermodels only, never physical evidence."""
import unittest
from check_smith_filsinger_restored_cycle_intervals import analyze

def I(a,b=None):
    return {'lower_J':str(a),'upper_J':str(a if b is None else b)}

class FirstLawAudit(unittest.TestCase):
    def setUp(self):
        self.work = {'original_id':'fixture','clock_id':'t','integration_remainder_certificate_required':True,
                     'net_environmental_work':I(3), 'net_controller_work':I(1), 'useful_load_work':I(2)}
        self.ind = {'original_id':'fixture','clock_id':'t','all_dissipative_and_outgoing_loss_J':I(2),
                    'total_stored_energy_final_minus_initial_J':I(0)}
    def test_exact_zero_residual_is_only_compatible(self):
        r=analyze(self.work,self.ind)
        self.assertTrue(r['zero_in_first_law_residual'])
        self.assertTrue(r['exact_restoration_admitted_by_interval'])
        self.assertFalse(r['f15_closed'])
    def test_outgoing_environmental_sink_excludes_natural_gain(self):
        self.work['net_environmental_work']=I(-2)
        r=analyze(self.work,self.ind)
        self.assertTrue(r['environmental_sink_proved_conditional_on_inputs'])
        self.assertEqual(r['first_law_residual_J'],I(-5))
        self.assertTrue(r['first_law_excluded_by_claimed_intervals'])
    def test_storage_drawdown_is_not_restoration(self):
        self.work['net_environmental_work']=I(1)
        self.ind['total_stored_energy_final_minus_initial_J']=I(-2)
        r=analyze(self.work,self.ind)
        self.assertFalse(r['exact_restoration_admitted_by_interval'])
        self.assertTrue(r['zero_in_first_law_residual'])
    def test_uncertainty_widens_residual_conservatively(self):
        self.work['net_environmental_work']=I(2,4)
        self.assertEqual(analyze(self.work,self.ind)['first_law_residual_J'],I(-1,1))
    def test_external_energy_not_independently_identified(self):
        self.assertFalse(analyze(self.work,self.ind)['physical_claim_closed'])
    def test_wrong_original_rejected(self):
        self.ind['original_id']='other'
        with self.assertRaisesRegex(ValueError,'apparatus'):
            analyze(self.work,self.ind)
    def test_wrong_clock_rejected(self):
        self.ind['clock_id']='another'
        with self.assertRaisesRegex(ValueError,'clock'):
            analyze(self.work,self.ind)
    def test_missing_remainder_admission_rejected(self):
        del self.work['integration_remainder_certificate_required']
        with self.assertRaisesRegex(ValueError,'remainder'):
            analyze(self.work,self.ind)
    def test_invalid_reversed_interval(self):
        self.ind['all_dissipative_and_outgoing_loss_J']=I(3,2)
        with self.assertRaisesRegex(ValueError,'reversed'):
            analyze(self.work,self.ind)
    def test_negative_loss_rejected(self):
        self.ind['all_dissipative_and_outgoing_loss_J']=I(-1)
        with self.assertRaisesRegex(ValueError,'negative'):
            analyze(self.work,self.ind)
    def test_float_rejected(self):
        self.ind['all_dissipative_and_outgoing_loss_J']={'lower_J':1.0,'upper_J':'2'}
        with self.assertRaisesRegex(ValueError,'exact rational'):
            analyze(self.work,self.ind)
    def test_unsigned_endpoint_is_rejected(self):
        self.work['useful_load_work']={'lower_J':'3'}
        with self.assertRaisesRegex(ValueError,'lower_J and upper_J'):
            analyze(self.work,self.ind)

if __name__ == '__main__': unittest.main()
