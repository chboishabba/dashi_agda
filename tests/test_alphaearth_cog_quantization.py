import sys
from pathlib import Path
import unittest
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from alphaearth_cog_quantization import decode_signed_int8, normalized_aggregate, aggregation_stability_bound

class Quantization(unittest.TestCase):
    def test_signed_nonlinear(self):
        raw=np.zeros((2,64),dtype=np.int8)
        raw[0,0]=127;raw[1,0]=-127
        dec=decode_signed_int8(raw)
        self.assertAlmostEqual(dec[0,0],(127/127.5)**2)
        self.assertAlmostEqual(dec[1,0],-(127/127.5)**2)
    def test_wrong_shape(self):
        with self.assertRaises(ValueError):decode_signed_int8(np.zeros((4,64),dtype=np.uint8))
    def test_aggregation(self):
        raw=np.zeros((2,64));raw[:,0]=[2,1]
        agg=normalized_aggregate(raw)
        self.assertAlmostEqual(agg[0],1.)
        self.assertAlmostEqual(np.linalg.norm(agg),1.)
    def test_cancel(self):
        raw=np.zeros((2,64));raw[:,0]=[1,-1]
        with self.assertRaises(ValueError):normalized_aggregate(raw)
    def test_stability(self):
        self.assertAlmostEqual(aggregation_stability_bound(2,.1),2*.1/(2-.1))
        with self.assertRaises(ValueError):aggregation_stability_bound(.1,.2)

if __name__=='__main__':unittest.main()
