#!/usr/bin/env python3
"""Source-specific SI field-scale cut; no empirical replication or device transfer.

Original experimental field: Pandey et al., RSC Advances (2019),
DOI 10.1039/C8RA09993F.
Original simulations: Kalita, Danovich & Shaik, JACS (2025),
DOI 10.1021/jacs.4c14791; Vargas-Rosales, Giangreco & Caflisch,
JPCB (2025), DOI 10.1021/acs.jpcb.5c04393.
Original authors retain all experiments and simulations.
"""
from fractions import Fraction
import json
import unittest

SOURCES = {
 "rsc_tau_2019": {"doi":"10.1039/C8RA09993F", "role":"in_vitro_peptide_electrode_experiment",
                 "ef_v_per_cm":(150,300), "frequency_hz":None,
                 "substrate":"synthetic PHF6 and PHF6* motifs"},
 "jacs_abeta_2025": {"doi":"10.1021/jacs.4c14791", "role":"molecular_dynamics_simulation",
                     "ef_v_per_angstrom":("0.01","0.0125","0.015","0.0175","0.02"),
                     "frequency_hz":(20_000_000,100_000_000,1_000_000_000),
                     "substrate":"A-beta models in molecular dynamics"},
 "jpcb_tau_2025": {"doi":"10.1021/acs.jpcb.5c04393", "role":"molecular_dynamics_simulation",
                   "ef_millivolt_per_nm":(100,200),
                   "frequency_hz":(100_000_000,1_000_000_000,10_000_000_000),
                   "substrate":"tau straight and paired-helical filament models"}
}
CONSUMER_MARKETING_HZ = 15  # Croft/Aurumaya attributed nominal label; not measured output

def v_per_m(number,unit):
    v=Fraction(str(number))
    factors={"V/cm":100,"V/angstrom":10_000_000_000,"mV/nm":1_000_000}
    if unit not in factors or v < 0:
        raise ValueError("incompatible field-strength unit or negative amplitude")
    return v*factors[unit]

def source_locked():
    experimental=tuple(v_per_m(v,"V/cm") for v in SOURCES["rsc_tau_2019"]["ef_v_per_cm"])
    jacs=tuple(v_per_m(v,"V/angstrom") for v in SOURCES["jacs_abeta_2025"]["ef_v_per_angstrom"])
    jpcb=tuple(v_per_m(v,"mV/nm") for v in SOURCES["jpcb_tau_2025"]["ef_millivolt_per_nm"])
    return {
        "sources":{k:{"doi":v["doi"],"role":v["role"],"substrate":v["substrate"]} for k,v in SOURCES.items()},
        "rsc_2019_V_per_m":list(map(int,experimental)),
        "jacs_2025_V_per_m":list(map(int,jacs)),
        "jpcb_2025_V_per_m":list(map(int,jpcb)),
        "jacs_max_over_rsc_max":str(max(jacs)/max(experimental)),
        "jpcb_min_over_rsc_max":str(min(jpcb)/max(experimental)),
        "jacs_min_freq_over_marketed_15Hz":str(Fraction(min(SOURCES["jacs_abeta_2025"]["frequency_hz"]),CONSUMER_MARKETING_HZ)),
        "jpcb_min_freq_over_marketed_15Hz":str(Fraction(min(SOURCES["jpcb_tau_2025"]["frequency_hz"]),CONSUMER_MARKETING_HZ)),
        "source_of_marketed_frequency":"historical/vendor label, no signal calibration",
        "jacs_2025_simulated_disaggregation_is_not_experiment":True,
        "jpcb_2025_simulated_tau_decay_is_not_human_therapy":True,
        "field_scale_ratio_is_not_dose_or_biological_effect_ratio":True,
        "B_field_magnetic_measurement_cannot_substitute_E_field":True,
        "electric_field_at_consumer_receiver_measured":False,
        "same_apparatus_exposure_or_specimen_join_authenticated":False,
        "original_2019_acs_full_methods_or_si_acquired":False,
    }

class TestSpecificSourceFieldScale(unittest.TestCase):
    def test_rsc_lower(self): self.assertEqual(v_per_m(150,"V/cm"),15000)
    def test_rsc_upper(self): self.assertEqual(v_per_m(300,"V/cm"),30000)
    def test_jacs_low(self): self.assertEqual(v_per_m("0.01","V/angstrom"),100000000)
    def test_jacs_high(self): self.assertEqual(v_per_m("0.02","V/angstrom"),200000000)
    def test_jpcb_low(self): self.assertEqual(v_per_m(100,"mV/nm"),100000000)
    def test_jpcb_high(self): self.assertEqual(v_per_m(200,"mV/nm"),200000000)
    def test_jacs_rsc_ratio(self): self.assertEqual(source_locked()["jacs_max_over_rsc_max"],"20000/3")
    def test_jpcb_rsc_ratio(self): self.assertEqual(source_locked()["jpcb_min_over_rsc_max"],"10000/3")
    def test_marketed_frequency_not_lab_calibration(self):
        self.assertEqual(source_locked()["jacs_min_freq_over_marketed_15Hz"],"4000000/3")
        self.assertFalse(source_locked()["electric_field_at_consumer_receiver_measured"])
    def test_reject_wrong_unit(self):
        with self.assertRaises(ValueError): v_per_m(1,"tesla")
    def test_reject_negative_strength(self):
        with self.assertRaises(ValueError): v_per_m(-1,"V/cm")
    def test_study_type_no_transfer(self):
        r=source_locked()
        self.assertFalse(r["same_apparatus_exposure_or_specimen_join_authenticated"])
        self.assertTrue(r["B_field_magnetic_measurement_cannot_substitute_E_field"])

if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser();p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    if a.self_test:
        res=unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(TestSpecificSourceFieldScale))
        raise SystemExit(0 if res.wasSuccessful() else 1)
    print(json.dumps(source_locked(),indent=2,sort_keys=True))
