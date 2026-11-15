"""Synthetic mathematical fixtures ONLY, never labeled as Omar MCG data."""
import importlib.util
from pathlib import Path
import unittest
import numpy as np
from scipy.signal import welch
SRC=Path(__file__).resolve().parents[1]/"scripts/nv_mcg_instrument_calibration.py"
spec=importlib.util.spec_from_file_location("nv_cal",SRC)
nv=importlib.util.module_from_spec(spec)
spec.loader.exec_module(nv)
class CalibrationFixture(unittest.TestCase):
    def test_lorentzian_recovery(self):
        f=np.linspace(2.86e9,2.88e9,1001)
        y=nv.lorentzian(f,10,1,2.87e9,7e5)
        o=nv.fit_odmr(np.column_stack([f,y]))
        self.assertTrue(o["converged"])
        self.assertLess(abs(o["center_hz"]-2.87e9),1.)
        self.assertLess(abs(o["fwhm_hz"]-1.4e6),1.)
        self.assertLess(o["fit_rms_signal"],1e-7)
    def test_psd_sensitivity_units(self):
        rng=np.random.default_rng(40)
        fs=200.
        t=np.arange(4000)/fs
        x=rng.standard_normal(len(t))
        o=nv.noise_asd(np.column_stack([t,x]),[20,30],2.)
        self.assertGreater(o["asd_median_signal_root_hz"],0)
        self.assertGreater(o["resolution_hz"],0)
    def test_publication_not_calibration(self):
        self.assertEqual(nv.SOURCES["JGU"]["reported_pt_root_hz"],13.)
        self.assertEqual(nv.SOURCES["ZAQuant"]["reported_pt_root_hz"],7.)
        self.assertEqual(nv.SOURCES["Q.ANT"]["reported_pt_root_hz"],26.)
if __name__=="__main__":unittest.main()
