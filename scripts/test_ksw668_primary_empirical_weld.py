#!/usr/bin/env python3
"""Offline regression tests: no invented external measurement files or URLs."""
import csv, math, tempfile, unittest
from pathlib import Path

import ksw668_neutron_spectrum_fold as Fold
import ksw668_mms_burst_acquire as MMS
import ksw668_movebank_gps_acquire as GPS
import check_ksw668_human_ams_original as AMS


class SourceWeldTests(unittest.TestCase):
    def _spectrum(self,unit="eV"):
        temp=tempfile.TemporaryDirectory()
        name=Path(temp.name)/"spectrum.csv"
        with name.open("w",newline="") as out:
            field="energy_eV" if unit=="eV" else "energy_MeV"
            writer=csv.DictWriter(out,[field,"differential_flux"])
            writer.writeheader()
            for i in range(1001):
                E=.01+.99*i/1000
                writer.writerow({field:E if unit=="eV" else E/1e6,
                                 "differential_flux":1.0 if unit=="eV" else 1e6})
        return temp,name

    def test_neutron_mev_ev_density_conversion(self):
        contexts=[self._spectrum(unit) for unit in ("eV","MeV")]
        try:
            rows_a,_,_=Fold.read_spectrum(contexts[0][1])
            rows_b,_,_=Fold.read_spectrum(contexts[1][1])
            a=Fold.fold(rows_a,1e20,"synthetic uniform source - TEST ONLY")
            b=Fold.fold(rows_b,1e20,"synthetic uniform source - TEST ONLY")
            self.assertAlmostEqual(a["modelled_in_window_reactions_per_second"],
                                   b["modelled_in_window_reactions_per_second"],places=12)
        finally:
            for ctx,_ in contexts:ctx.cleanup()

    def test_neutron_analytic_power_law_integral(self):
        ctx,path=self._spectrum()
        try:
            rows,_,_=Fold.read_spectrum(path)
            got=Fold.fold(rows,1e20,"synthetic constant differential flux")
            exact=1e20*1e-24*Fold.A*(1**(Fold.B+1)-(.01)**(Fold.B+1))/(Fold.B+1)
            self.assertAlmostEqual(got["modelled_in_window_reactions_per_second"]/exact,1,
                                   delta=.0002)
            self.assertGreater(got["fit_covariance_only_sigma_per_second"],0)
        finally:ctx.cleanup()

    def test_neutron_no_extrapolation(self):
        with self.assertRaises(ValueError):
            Fold.fold([(1.9,1.0),(100.0,1.0)],1e20,"synthetic")
        with self.assertRaises(ValueError):
            Fold.fold([(.01,1.0),(.1,1.0)],1e20,"")

    def test_original_mms_event_overlap_and_unrelated_time(self):
        self.assertTrue(MMS.overlaps("2017-06-17/20:24:02",
                                     "2017-06-17/20:24:12"))
        self.assertFalse(MMS.overlaps("2017-06-17/20:20:02",
                                      "2017-06-17/20:20:12"))

    def test_mms_signed_jdot_eprime_units(self):
        ep,val=MMS.eprime_and_work([1,0,0],[1,0,0],[0,1,0],[0,0,1000])
        self.assertAlmostEqual(ep[0],2.0)
        self.assertAlmostEqual(val,.002)  # 1 nA/m² x 2 mV/m = .002 nW/m³

    def test_gps_synthetic_file_does_not_infer_treatment(self):
        raw=("individual-local-identifier,location-lat,location-long,timestamp\n"
             "birdA,47.1,9.2,2026-05-21T12:00:00Z\n"
             "birdA,47.2,9.1,2026-05-21T12:00:05Z\n").encode()
        result=GPS.validate_gps(raw)
        self.assertEqual(result["gps_fixes_with_coords"],2)
        self.assertEqual(result["animals_in_file"],1)
        self.assertFalse(result["treatment_join_present"])
        self.assertFalse(result["homing_endpoint_reconstructed"])

    def test_gps_reject_html(self):
        with self.assertRaises(ValueError):
            GPS.validate_gps(b"<html><body>Access denied</body></html>")

    def test_original_2013_human_ams_sample_census(self):
        r=AMS.inspect(AMS.DEFAULT)
        self.assertEqual(r["assays"],34)
        self.assertEqual(r["distinct_donors"],28)
        self.assertEqual(r["source_flagged_outlier_assays"],5)
        pairs={p["donor_ref"]:p for p in r["same_donor_tissue_comparisons"]}
        self.assertAlmostEqual(pairs["24"]["diff_pMC"],25.75)
        self.assertAlmostEqual(pairs["26"]["diff_pMC"],38.69)
        self.assertTrue(pairs["25"]["source_outliers"])
        self.assertTrue(pairs["28"]["source_outliers"])


if __name__=="__main__":
    unittest.main(verbosity=2)
