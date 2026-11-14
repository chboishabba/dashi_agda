#!/usr/bin/env python3
"""B2 no-network exact tetra source-equivalent and raw-provenance controls.

No original MMS E/B/J/ephemeris CDF bytes are fabricated or downloaded.
"""
import unittest
import math
import ksw668_mms4_tetrahedron_boundary as B
import ksw668_mms_sdc_direct as SDC

class TetPoyntingTests(unittest.TestCase):
    def test_exact_synthetic_maxwell_plane_wave(self):
        receipt=B.synthetic_plane_wave()
        self.assertEqual(receipt["status"],"SYNTHETIC MATHEMATICAL TEST ONLY")
        self.assertTrue(receipt["synthetic_maxwell_plane_wave_residual_verified"])
        self.assertGreater(abs(receipt["integrated_outward_poynting_J"]),0)
        self.assertFalse(receipt["source_physical_boundary_empirically_accepted"])
        self.assertEqual(receipt["source_raw_CDF_files_verified"],0)

    def test_quadratic_face_integral_source_exact(self):
        # On [0,L] reference tetra, E=(0,x,0), B=(0,0,x):
        # div(E cross B) = 2x. Exact surface flux = L^4/(12*mu0).
        L=2.0
        ref=[(0.,0.,0.),(L,0.,0.),(0.,L,0.),(0.,0.,L)]
        E=[(0.,p[0],0.) for p in ref]
        M=[(0.,0.,p[0]) for p in ref]
        flux,area=B.surface_flux(ref,E,M)
        self.assertAlmostEqual(flux,L**4/(12*B.MU0),
                               delta=2e-10*abs(flux))
        self.assertGreater(area,0)

    def test_exact_affine_volume_bilinear(self):
        L=2.
        V=L**3/6
        v=[(p,0,0) for p in (0,L,0,0)]
        self.assertAlmostEqual(B.integral_bilinear_tetra(v,v,V),
                               V*L*L/10)

    def test_tetra_degenerate_is_rejected(self):
        coplanar=[(0,0,0),(1,0,0),(0,1,0),(.5,.5,0)]
        with self.assertRaises(ValueError):
            B.barycentric(coplanar,(.2,.2,0))


    def test_original_SDC_four_probe_burst_selector(self):
        for probe in (1,2,3,4):
            filename=(f"mms{probe}_fgm_brst_l2_20170617202400_v1.0.0.cdf")
            result=SDC.select_near_event([filename],10,probe,["fgm"])
            self.assertEqual(result["fgm"][0]["filename"],filename)
            self.assertIn("sc_id=mms"+str(probe),SDC.make_listing_url(probe))
            wrong=(probe%4)+1
            with self.assertRaises(ValueError):
                SDC.select_near_event([filename],10,wrong,["fgm"])

    def test_wrong_or_missing_original_raw_is_not_accepted(self):
        item={"id":"mms1","sample_time_utc":"2017-06-17T20:24:04Z",
             "position_GSE_km":[0,0,0],"E_GSE_mV_m":[0,1,0],
             "B_GSE_nT":[0,0,1],"J_GSE_nA_m2":[0,0,0],
             "E_component_abs_error_mV_m":.01,
             "B_component_abs_error_nT":.01,
             "J_component_abs_error_nA_m2":.01,
             "quality_E":"pass","quality_B":"pass","quality_J":"pass"}
        with self.assertRaises(ValueError):
            B.verify_sources(item,{}) # No original bytes, no independent source
        item["id"]="mms1"
        with self.assertRaises(ValueError):
            B.epoch({"time_utc":"2017-06-17T20:24:04Z",
                     "spacecraft":[item,item,item,item]}, {},True)
        with self.assertRaises(ValueError):
            B.analyze({"schema":"dashi.ksw668.mms4-tetra-original-v1",
                       "reference_frame":"GSE",
                       "spatial_model":"affine_4_spacecraft_interpolation",
                       "epochs":[]},False)

if __name__=="__main__":
    unittest.main(verbosity=2)
