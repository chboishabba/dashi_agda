import sys
from pathlib import Path
import unittest
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from cross_model_alignment import fit_alignment

class Alignment(unittest.TestCase):
    def test_valid(self):
        rng=np.random.default_rng(3)
        a=rng.normal(size=(80,64)); t=np.c_[a,a]
        tr=np.arange(80)<60; te=~tr
        receipt=fit_alignment(a,t,tr,te,latent=8)
        self.assertEqual(receipt['test_count'],20)
        self.assertLess(receipt['matched_heldout_mean_distance'],.00001)
    def test_overlap_rejected(self):
        a=np.zeros((10,64));t=np.zeros((10,128)); tr=np.ones(10,bool);te=tr.copy()
        with self.assertRaises(ValueError):fit_alignment(a,t,tr,te,latent=2)

if __name__=='__main__':unittest.main()
