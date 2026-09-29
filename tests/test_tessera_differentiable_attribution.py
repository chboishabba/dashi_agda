"""Synthetic differentiable-sensor and physical-probe tests.

These tests exercise the actual runtime adapter with a deterministic surrogate
model. They do NOT claim a pretrained TESSERA checkpoint or Woogaroo data ran.
"""
import sys
from pathlib import Path
import unittest
from types import SimpleNamespace
import numpy as np
import torch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import tessera_differentiable_attribution as adapter
from train_tessera_physical_probes import prepare,train_prefix

class MockInfer:
    @staticmethod
    def get_bin_size(n):
        return max(8,int(np.ceil(n/8))*8) if n>0 else 0
    @staticmethod
    def _pad_pattern(n,b):
        return np.arange(b)%n

def fake_student():
    return SimpleNamespace(
      S2_BAND_MEAN=np.zeros(10,dtype=np.float32),
      S2_BAND_STD=np.ones(10,dtype=np.float32),
      S1A_BAND_MEAN=np.zeros(2,dtype=np.float32),
      S1A_BAND_STD=np.ones(2,dtype=np.float32),
      S1D_BAND_MEAN=np.zeros(2,dtype=np.float32),
      S1D_BAND_STD=np.ones(2,dtype=np.float32))

class MockStudent(torch.nn.Module):
    """Intentionally differentiable deterministic 128D synthetic encoder."""
    def encode(self,s2,s1):
        e=torch.cat([s2[:,:,:10].mean(dim=1),s1[:,:,:2].mean(dim=1)],dim=-1)
        return torch.nn.functional.pad(e,(0,116))


class TestDifferentiableAdapter(unittest.TestCase):
    def fixtures(self):
        s2=np.ones((1,3,10),dtype=np.float32)
        doy=np.array([[20,30,40]])
        mask=np.array([[1,0,1]])
        asc=np.array([[[2.,3.],[0.,0.]]],dtype=np.float32)
        adoy=np.array([[20,30]])
        desc=np.array([[[4.,5.]]],dtype=np.float32)
        ddoy=np.array([[40]])
        return (s2,doy,mask,asc,adoy,desc,ddoy)
    def test_selection_retains_fixed_masks_and_binning(self):
        inputs,raw,meta=adapter.prepare_torch(*self.fixtures(),MockInfer,fake_student())
        self.assertEqual(meta['s2_valid_count'],2)
        self.assertEqual(meta['s1_valid_count'],2)
        self.assertEqual(inputs[0].shape,(1,8,11))
        self.assertEqual(inputs[1].shape,(1,8,3))
        self.assertNotIn(1,meta['s2_original_indices'])
        self.assertNotIn(1,meta['s1_merged_indices'])
        self.assertEqual(meta['s1_merged_indices'][0:2],[0,2])
    def test_jacobian_matches_finite_difference(self):
        args=self.fixtures()
        inputs,raw,meta=adapter.prepare_torch(*args,MockInfer,fake_student())
        embedding,pred,grad=adapter.jacobians(MockStudent(),inputs,raw,prefix=16)
        self.assertEqual(embedding.shape,(1,128))
        self.assertEqual(grad[0].shape,(16,1,3,10))
        self.assertAlmostEqual(float(grad[0][0,0,1,0]),0.,places=7)
        self.assertAlmostEqual(float(grad[0][0,0,0,0]),.5,places=6)
        eps=1e-3
        modified=list(args)
        modified[0]=args[0].copy()
        modified[0][0,0,0]+=eps
        inputs2,raw2,_=adapter.prepare_torch(*modified,MockInfer,fake_student())
        target=MockStudent().encode(*inputs2)[0,0].item()
        self.assertAlmostEqual((target-embedding[0,0])/eps,grad[0][0,0,0,0],places=3)
    def test_integrated_gradients_completeness(self):
        inputs,raw,_=adapter.prepare_torch(*self.fixtures(),MockInfer,fake_student())
        result=adapter.integrated_gradients(MockStudent(),inputs,raw,prefix=16,decoder=None,steps=8)
        self.assertLess(result['completeness_residual'],1e-5)
    def test_bad_mask_and_doy(self):
        args=list(self.fixtures())
        args[2]=np.array([[1,2,1]])
        with self.assertRaises(ValueError):
            adapter.prepare_torch(*args,MockInfer,fake_student())
    def test_supervised_holdout_and_prefix(self):
        rng=np.random.default_rng(7)
        n=60
        e=rng.normal(size=(n,128))
        y=(3*e[:,0]-2*e[:,1])[:,None]
        records=dict(tessera=e,labels=y,
          cell=np.array([f'cell{i//2}' for i in range(n)]),
          year=np.array([2019 if i%2==0 else 2024 for i in range(n)]),
          label_source=np.array(['independent-synthetic-test']*n))
        v,y,tr,te,receipt=prepare(records,['cell25','cell26','cell27','cell28','cell29'],['2024'])
        head,metrics=train_prefix(v,y,tr,te,16)
        self.assertEqual(head['weight'].shape,(1,16))
        self.assertLess(metrics['MAE'],1)
        self.assertEqual(receipt['test_rows'],5)

if __name__=="__main__":
    unittest.main()
