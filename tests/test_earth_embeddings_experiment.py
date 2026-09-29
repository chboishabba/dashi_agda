"""Synthetic unit tests for Earth embedding evaluation; no real Woogaroo claims."""
import sys
from pathlib import Path
import unittest
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from earth_embeddings_experiment import (split_by_spatial_and_temporal_holdout,
    participation_ratio, local_pca_tangents, tangent_rotation_angles,
    normalized_quantization_error, evaluate)

def sample():
    rng = np.random.default_rng(23)
    n = 24
    return dict(alpha=rng.normal(size=(n,64)), tessera=rng.normal(size=(n,128)),
      baseline=rng.normal(size=(n,3)), labels=rng.normal(size=n),
      cell=np.array([f'cell{i//2}' for i in range(n)]),
      year=np.array([2018 if i%2 == 0 else 2024 for i in range(n)]),
      x=np.arange(n,dtype=float)*100, y=np.zeros(n),
      label_source=np.array(['synthetic']*n))

class Tests(unittest.TestCase):
    def test_split_and_four_heads(self):
        data=sample()
        tr, te=split_by_spatial_and_temporal_holdout(data, ['2024'], [f'cell{i}' for i in range(9,12)])
        self.assertEqual(int(te.sum()),3)
        self.assertGreater(int(tr.sum()),0)
        receipt=evaluate(data, {}, tr, te)
        self.assertEqual(set(receipt['metrics']), {'M0_static','MA_alpha','MT_tessera','MAT_fused'})
        self.assertTrue(all(np.isfinite(item['RMSE']) for item in receipt['metrics'].values()))
    def test_buffer(self):
        data=sample()
        tr,te=split_by_spatial_and_temporal_holdout(data,['2024'], ['cell11'],500)
        self.assertTrue(tr.sum() > 0)
        self.assertTrue(np.min(np.abs(data['x'][tr,None]-data['x'][None,te])) >= 500)
    def test_empty_split(self):
        with self.assertRaises(ValueError):
            split_by_spatial_and_temporal_holdout(sample(), ['1999'], ['missing'])
    def test_participation_rank1(self):
        v=np.arange(1,21)[:,None]*np.array([[1.,2.,3.]])
        self.assertAlmostEqual(participation_ratio(v),1.,places=6)
    def test_tangents(self):
        data=np.random.default_rng(2).normal(size=(30,5))
        angles=tangent_rotation_angles(local_pca_tangents(data,k=8,intrinsic=2))
        self.assertAlmostEqual(angles[0],0.,places=5)
        self.assertTrue(all(0<=a<=90.000001 for a in angles))
    def test_quantisation(self):
        a=np.ones((3,64))
        b=a+0.1
        result=normalized_quantization_error(a,b,.1)
        self.assertLessEqual(result['max_l2_error'],result['certified_l2_upper_bound']+1e-8)
        with self.assertRaises(ValueError):
            normalized_quantization_error(a,b,.01)

if __name__ == '__main__':
    unittest.main()
