from __future__ import annotations
import copy
from fractions import Fraction as F
import unittest
import check_hardt_rai_lagged_common_source as m

class TestRaiCausalAcceptance(unittest.TestCase):
    def test_original_method_reconstruction_not_claimed(self):
        x=m.audit_method(m.METHOD)
        self.assertEqual(x['nominal_window_hop_seconds'],'1')
        self.assertFalse(x['reproduced_CCA'])
    def test_actual_original_granger_not_claimed(self):
        x=m.causal_common_source_witness()
        self.assertFalse(x['original_EEG_or_study_Granger_reproduced'])
    def test_predictive_improvement_without_direct_causal_link(self):
        x=m.causal_common_source_witness()
        self.assertTrue(x['predictive_lag_improvement'])
        self.assertEqual(x['heldout_Ypast_plus_Xpast_MSE'],'0')
        self.assertFalse(x['direct_X_to_Y_edge_in_SCM'])
    def test_observed_cue_as_good_as_lagged_x(self):
        x=m.causal_common_source_witness()
        self.assertEqual(x['heldout_Ypast_plus_original_source_MSE'],'0')
        self.assertGreater(F(x['heldout_Ypast_only_MSE']),0)
    def test_intervention_does_not_change_outcome(self):
        self.assertFalse(m.causal_common_source_witness()['do_X_changes_Y_in_declared_SCM'])
    def test_wrong_band_rejected(self):
        x=copy.deepcopy(m.METHOD);x['band_hz']=[2,4]
        with self.assertRaisesRegex(ValueError,'method metadata'):m.audit_method(x)
    def test_wrong_5s_or_80pct_rejected(self):
        for k,v in [('window_seconds',4),('overlap_percent',50)]:
            x=copy.deepcopy(m.METHOD);x[k]=v
            with self.assertRaisesRegex(ValueError,'method metadata'):m.audit_method(x)
    def test_random_null_count_rejected(self):
        x=copy.deepcopy(m.METHOD);x['surrogates']=100
        with self.assertRaisesRegex(ValueError,'method metadata'):m.audit_method(x)
    def test_null_distribution_not_replayed(self):
        x=m.audit_method(m.METHOD)
        self.assertFalse(x['reproduced_1000_shift_null'])
        self.assertFalse(x['reproduced_cluster_FWER'])
    def test_singular_design_rejected(self):
        with self.assertRaisesRegex(ValueError,'singular'):m.solve([[1,1],[1,1]],[0,0])
    def test_source_OLS_has_no_regression_error(self):
        xx=m.causal_common_source_witness()
        self.assertEqual(xx['heldout_Ypast_plus_original_source_MSE'],'0')
    def test_1000_shift_null_significant_despite_only_common_cue(self):
        x=m.circular_shift_shared_cue_null()
        self.assertEqual(x['null_permutations'],1000)
        self.assertEqual(x['synthetic_permutation_tail_probability'],'1/1001')
        self.assertFalse(x['direct_brain_to_brain_edge_in_model'])

    def test_surrogate_metric_is_not_Rai_CCA(self):
        self.assertFalse(m.circular_shift_shared_cue_null()['original_Rai_CCA_or_clusters_reproduced'])

    def test_correlation_zero_variance_rejected(self):
        with self.assertRaisesRegex(ValueError,'zero-variance'):
            m.squared_pearson_int([1,1,1],[1,-1,1])

    def test_provenance_lock_rejected(self):
        x=copy.deepcopy(m.METHOD);x['paper_doi']='another-paper'
        with self.assertRaisesRegex(ValueError,'method metadata'):m.audit_method(x)

if __name__=='__main__':unittest.main()
