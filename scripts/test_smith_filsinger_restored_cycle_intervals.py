"""Synthetic exact-rational countermodels only, never physical evidence."""
import unittest
from check_smith_filsinger_restored_cycle_intervals import analyze

def I(a,b=None):
    return {'lower_J':str(a),'upper_J':str(a if b is None else b)}

class FirstLawAudit(unittest.TestCase):
    def setUp(self):
        self.work = {'original_id':'fixture','clock_id':'t','integration_remainder_certificate_required':True,
                     'signed_balance_from_named_port_role_map':True,
                     'conditional_port_work':{
                         'natural_incident':I(5), 'natural_outgoing':I(2),
                         'controller_incident':I(2), 'controller_outgoing':I(1),
                         'load_output':I(2)},
                     'net_environmental_work':I(3), 'net_controller_work':I(1),
                     'useful_load_work':I(2),
                     'unassigned_loss_or_storage_change':I(2)}
        self.ind = {'original_id':'fixture','clock_id':'t','all_dissipative_and_outgoing_loss_J':I(2),
                    'total_stored_energy_final_minus_initial_J':I(0)}
    def test_exact_zero_residual_is_only_compatible(self):
        r=analyze(self.work,self.ind)
        self.assertTrue(r['zero_in_first_law_residual'])
        self.assertTrue(r['exact_restoration_admitted_by_interval'])
        self.assertFalse(r['f15_closed'])
    def test_outgoing_environmental_sink_excludes_natural_gain(self):
        self.work['conditional_port_work']['natural_incident']=I(0)
        self.work['net_environmental_work']=I(-2)
        self.work['unassigned_loss_or_storage_change']=I(-3)
        r=analyze(self.work,self.ind)
        self.assertTrue(r['environmental_sink_proved_conditional_on_inputs'])
        self.assertEqual(r['first_law_residual_J'],I(-5))
        self.assertTrue(r['first_law_excluded_by_claimed_intervals'])
    def test_storage_drawdown_is_not_restoration(self):
        self.work['conditional_port_work']['natural_incident']=I(3)
        self.work['net_environmental_work']=I(1)
        self.work['unassigned_loss_or_storage_change']=I(0)
        self.ind['total_stored_energy_final_minus_initial_J']=I(-2)
        r=analyze(self.work,self.ind)
        self.assertFalse(r['exact_restoration_admitted_by_interval'])
        self.assertTrue(r['zero_in_first_law_residual'])
    def test_uncertainty_widens_residual_conservatively(self):
        self.work['conditional_port_work']['natural_incident']=I(4,6)
        self.work['net_environmental_work']=I(2,4)
        self.work['unassigned_loss_or_storage_change']=I(1,3)
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

    def test_reject_tampered_natural_summary(self):
        self.work['net_environmental_work']=I(500)
        with self.assertRaisesRegex(ValueError,'disagrees with net_environmental_work'):
            analyze(self.work,self.ind)
    def test_reject_tampered_load_summary(self):
        self.work['useful_load_work']=I(0)
        with self.assertRaisesRegex(ValueError,'disagrees with useful_load_work'):
            analyze(self.work,self.ind)
    def test_reject_tampered_unassigned_summary(self):
        self.work['unassigned_loss_or_storage_change']=I(500)
        with self.assertRaisesRegex(ValueError,'disagrees with unassigned'):
            analyze(self.work,self.ind)
    def test_reject_missing_named_port(self):
        del self.work['conditional_port_work']['natural_outgoing']
        with self.assertRaisesRegex(ValueError,'five-port'):
            analyze(self.work,self.ind)
    def test_reject_missing_signed_role_receipt(self):
        del self.work['signed_balance_from_named_port_role_map']
        with self.assertRaisesRegex(ValueError,'signed port-role map'):
            analyze(self.work,self.ind)

if __name__ == '__main__': unittest.main()
